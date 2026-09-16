import RumocaC.InvocationFootprint
import RumocaFMI3.ReleaseTail

namespace Rumoca.FMI3.StaticRelease.Capture
open CTree CMemory CCalls

/-- Only the prefix that still has to read the instance's slot metadata
requires its value frame. Captured atomic arguments and the return suffix do
not read that metadata again. -/
def needsMetadata : Typed.State → Bool
  | .calling name _ _ _ => name == function.signature.name
  | .body (.running code _ _ _) _ _ => match code with
      | [.ret none] => false
      | _ => true
  | _ => false

def footprint (p : Option Address) (state : Typed.State) : Set Address :=
  if needsMetadata state then {q | ∃ address, p = some address ∧ q = address.member "slot"} else ∅

def Protected (p : Option Address) (flags : Address) (slot : Nat) (state : Typed.State) : Prop :=
  (ConcurrentInvariant.Ready p flags slot .done state ∧
    (needsMetadata state = true → ConcurrentInvariant.Metadata p slot (CReadOnly.typedHeap state))) ∨
  VoidReturn.Ready (locals p) types state

theorem needsMetadata_withHeap (state : Typed.State) (heap : Heap) :
    needsMetadata (Concurrent.withHeap state heap) = needsMetadata state := by
  cases state with
  | body state => cases state <;> rfl
  | calling | kernel | returning | halted => rfl

theorem protected_frame (ready : Protected p flags slot state)
    (frame : Set.EqOn (CReadOnly.typedHeap state) heap (footprint p state)) :
    Protected p flags slot (Concurrent.withHeap state heap) := by
  rcases ready with ⟨control, metadata⟩ | tail
  · refine .inl ⟨control.withHeap heap, ?_⟩
    rw [needsMetadata_withHeap]
    intro needed
    have stable : ConcurrentInvariant.MetadataFrame p (CReadOnly.typedHeap state) heap := by
      intro address selected
      exact (frame (by simp [footprint, needed, selected])).symm
    simpa only [Concurrent.heap_withHeap] using (metadata needed).preserved stable
  · exact .inr (tail.withHeap heap)

theorem captured_footprint (args : List Value) (heap : Heap) (stack : Typed.Continuation) :
    footprint p (.calling "atomic_store" args heap stack) = ∅ := by
  simp [footprint, needsMetadata, function]

theorem tail_footprint (tail : VoidReturn.Ready (locals p) types state) : footprint p state = ∅ := by
  cases tail <;> rfl

variable [interface : CInterface] {E : Type}

/-- The release's own actual steps preserve the protected control. After
operand capture no metadata premise is needed, including for the atomic step. -/
theorem step_protected (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (bindings : StaticRelease.Bindings program tag)
    (flagsBound : interface.constants "rumoca_instance_flags" = some (.pointer (some flags)))
    (ready : Protected p flags slot before) (step : Events.Step program before events after) :
    Protected p flags slot after := by
  rcases ready with ⟨control, metadata⟩ | tail
  · have advancePrefix : ∀ state, ConcurrentInvariant.Ready p flags slot .done state →
        ConcurrentInvariant.Metadata p slot (CReadOnly.typedHeap state) → ¬ Concurrent.Exit .done state →
        Events.Step program state events after → Protected p flags slot after := by
      intro state current values active actual
      obtain ⟨following, preserved⟩ := ConcurrentInvariant.step_ready program tag bindings flagsBound current values active actual
      exact .inl ⟨following, fun _ => values.preserved preserved⟩
    cases control with
    | entry heap =>
      exact advancePrefix _ (.entry heap) (metadata (by simp [needsMetadata])) (by simp [Concurrent.Exit]) step
    | parameters heap =>
      exact advancePrefix _ (.parameters heap) (metadata (by simp [needsMetadata, function])) (by simp [Concurrent.Exit]) step
    | guarded heap =>
      exact advancePrefix _ (.guarded heap) (metadata rfl) (by simp [Concurrent.Exit]) step
    | clear address heap =>
      exact advancePrefix _ (.clear address heap) (metadata rfl) (by simp [Concurrent.Exit]) step
    | atomic address heap =>
      exact .inr (StaticRelease.clear_return_tail program tag bindings.boolean bindings.atomicPointer bindings.atomicBound
        (.atomic address heap) rfl step).2.2
    | resumed address heap => exact .inr (VoidReturn.step_ready program (.resumed heap) step).2.1
    | returning heap => exact .inr (VoidReturn.step_ready program (.returning heap) step).2.1
    | returned heap => exact .inr (VoidReturn.step_ready program (.returned heap) step).2.1
    | done heap => exact .inr (VoidReturn.step_ready program (.done heap) step).2.1
  · exact .inr (VoidReturn.step_ready program tail step).2.1

omit interface in
/-- Recover the emitted operands and saved root continuation from reached
protected control. Neither is supplied by the caller as a success assumption. -/
theorem atomic_control (ready : Protected p flags slot (.calling name args heap stack))
    (atomic : name = "atomic_store") :
    p.isSome = true ∧ args = [.pointer (some (flags.index slot)), CAtomicBoolean.value false] ∧
      stack = .caller .discard [.ret none] (locals p) types "void" .done := by
  rcases ready with ⟨control, _⟩ | tail
  · cases control with
    | entry => simp [function] at atomic
    | atomic address => exact ⟨rfl, rfl, rfl⟩
  · cases tail

/-- The frame follows current control under the original invocation serial.
Other factories may reuse the record after the real clear without preserving
its old metadata. No fairness or successful completed call is assumed. -/
theorem history_protected (program : Events.Program E) (policy : Host.Policy)
    (tag : CAtomicBoolean.Calls.Event → E) (bindings : StaticRelease.Bindings program tag)
    (flagsBound : interface.constants "rumoca_instance_flags" = some (.pointer (some flags)))
    (issued : serial < before.ledger.next)
    (ready : Host.Recording.CurrentSelected (Protected p flags slot) tracked serial before)
    (path : Transition.Events.Reaches
      (fun a ticks b => Host.Recording.Step program policy a ticks b ∧
        Host.Recording.FootprintFrame (footprint p) tracked serial a ticks b)
      before ticks after) :
    serial < after.ledger.next ∧ Host.Recording.CurrentSelected (Protected p flags slot) tracked serial after ∧
      Transition.Events.Reaches (Host.Recording.Step program policy) before ticks after :=
  Host.Recording.current_footprint_history program policy (Protected p flags slot) (footprint p)
    (fun _ _ h frame => protected_frame h frame)
    (fun _ _ _ h actual => step_protected program tag bindings flagsBound h actual) issued ready path

end Rumoca.FMI3.StaticRelease.Capture
