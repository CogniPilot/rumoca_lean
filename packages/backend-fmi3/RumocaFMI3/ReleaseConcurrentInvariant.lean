import RumocaFMI3.ReleaseInvariant
import RumocaC.CallHeapIntervals

/-! Preserve release pointer origin under explicit other-thread metadata interference. -/
namespace Rumoca.FMI3.StaticRelease.ConcurrentInvariant
open CTree CMemory CCalls
open CCalls.Concurrent (Exit BeforeReturn)
variable [interface : CInterface] {E : Type}

def CurrentReady (p : Option Address) (flags : Address) (slot : Nat)
    (stack : Typed.Continuation) (tracked : Nat) (state : Concurrent.State) : Prop :=
  ∃ saved, state.threads tracked = some saved ∧
    Ready p flags slot stack (Concurrent.withHeap saved state.heap) ∧ Metadata p slot state.heap

/-- The environment frame constrains only other threads, not this release's
execution. The tracked release derives its own metadata frame in `step_ready`. -/
def EnvironmentFrame (p : Option Address) (tracked : Nat)
    (before : Concurrent.State) (chosen : Nat) (after : Concurrent.State) : Prop :=
  chosen ≠ tracked → MetadataFrame p before.heap after.heap

theorem thread_step (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (bindings : StaticRelease.Bindings program tag)
    (flagsBound : interface.constants "rumoca_instance_flags" = some (.pointer (some flags)))
    (ready : CurrentReady p flags slot stack tracked before)
    (active : BeforeReturn tracked stack before chosen)
    (frame : EnvironmentFrame p tracked before chosen after)
    (step : Concurrent.Step program before chosen events after) :
    CurrentReady p flags slot stack tracked after := by
  let P := fun state => Ready p flags slot stack state ∧ Metadata p slot (CReadOnly.typedHeap state)
  have preserves : ∀ state events target, P state → ¬ Exit stack state →
      Events.Step program state events target → P target := by
    intro state events target ready active step
    obtain ⟨next, frame⟩ := step_ready program tag bindings flagsBound ready.1 ready.2 active step
    exact ⟨next, ready.2.preserved frame⟩
  obtain ⟨saved, selected, control, metadata⟩ := ready
  have start : ∃ saved, before.threads tracked = some saved ∧ P (Concurrent.withHeap saved before.heap) :=
    ⟨saved, selected, control, by simpa only [Concurrent.heap_withHeap] using metadata⟩
  have environment : chosen ≠ tracked → ∀ saved, before.threads tracked = some saved →
      P (Concurrent.withHeap saved before.heap) → P (Concurrent.withHeap saved after.heap) := by
    intro different saved selected ready
    refine ⟨?_, ?_⟩
    · simpa only [Concurrent.withHeap_twice] using ready.1.withHeap after.heap
    · simpa only [Concurrent.heap_withHeap] using
        (show Metadata p slot before.heap from by simpa only [Concurrent.heap_withHeap] using ready.2).preserved (frame different)
  obtain ⟨saved, selected, ready⟩ := Concurrent.framed_predicate_step program P before after tracked chosen
    preserves environment start active step
  exact ⟨saved, selected, ready.1, by simpa only [Concurrent.heap_withHeap] using ready.2⟩

theorem thread_reaches (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (bindings : StaticRelease.Bindings program tag)
    (flagsBound : interface.constants "rumoca_instance_flags" = some (.pointer (some flags)))
    (ready : CurrentReady p flags slot stack tracked before)
    (path : Transition.Reaches (fun a b => ∃ chosen events,
      Concurrent.Step program a chosen events b ∧ BeforeReturn tracked stack a chosen ∧
        EnvironmentFrame p tracked a chosen b) before after) :
    CurrentReady p flags slot stack tracked after := by
  induction path with
  | refl => exact ready
  | next first rest ih =>
    obtain ⟨chosen, events, step, active, frame⟩ := first
    exact ih (thread_step program tag bindings flagsBound ready active frame step)

/-- Every release call in this invocation uses its original metadata index.
No successful complete call or converted argument shape is assumed. Other
threads must retain that metadata until the tracked invocation returns. -/
theorem call_prefix_origin (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (bindings : StaticRelease.Bindings program tag)
    (flagsBound : interface.constants "rumoca_instance_flags" = some (.pointer (some flags)))
    (entry : before.threads tracked = some (.calling function.signature.name [.pointer p] savedHeap stack))
    (metadata : Metadata p slot before.heap)
    (path : Transition.Reaches (fun a b => ∃ chosen events,
      Concurrent.Step program a chosen events b ∧ BeforeReturn tracked stack a chosen ∧
        EnvironmentFrame p tracked a chosen b) before after) :
    (∀ args heap later, after.threads tracked = some (.calling "atomic_store" args heap later) →
      p.isSome = true ∧ args = [.pointer (some (flags.index slot)), CAtomicBoolean.value false]) ∧
    (∀ value heap, after.threads tracked = some (.returning value heap stack) → value = .void) ∧
    Metadata p slot after.heap := by
  obtain ⟨saved, selected, ready, metadata⟩ := thread_reaches program tag bindings flagsBound
    (show CurrentReady p flags slot stack tracked before from ⟨_, entry, .entry _, metadata⟩) path
  refine ⟨?_, ?_, metadata⟩
  · intro args heap later calling
    cases Option.some.inj (selected.symm.trans calling)
    exact ready.atomic_origin rfl
  · intro value heap returning
    cases Option.some.inj (selected.symm.trans returning)
    exact ready.exit_value

end Rumoca.FMI3.StaticRelease.ConcurrentInvariant
