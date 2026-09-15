import RumocaC.StoreInvariant
import RumocaC.CallLinkage
import RumocaC.ConcurrentCalls

/-! Lift store-stable heap relations through calls and modeled interleavings; attribute relation changes to actual foreign executions. -/
noncomputable section
namespace Rumoca.CStoreInvariant
open CTree CMemory CCalls CCalls.Events
variable [CInterface] {E : Type}

def ExternalPreserves (R : Heap → Heap → Prop) (fn : External E) : Prop :=
  ∀ args before events result after, fn.execute args before events result after → R before after

def ProgramPreserves (R : Heap → Heap → Prop) (program : Events.Program E) : Prop :=
  ∀ name fn, program.externals name = some fn → ExternalPreserves R fn

variable {R : Heap → Heap → Prop}

theorem event_next (stable : Stable R) (foreign : ProgramPreserves R program)
    (step : Events.Step program s events t) :
    R (CReadOnly.typedHeap s) (CReadOnly.typedHeap t) := by
  cases step with
  | internal step => exact internal_next stable _ step
  | external found converted executed => exact foreign _ _ found _ _ _ _ _ executed

theorem event_reaches (stable : Stable R)
    (trans : ∀ {a b c}, R a b → R b c → R a c)
    (foreign : ProgramPreserves R program)
    (path : Transition.Events.Reaches (Events.machine program).step s events t) :
    R (CReadOnly.typedHeap s) (CReadOnly.typedHeap t) := by
  induction path with
  | refl => exact stable.refl _
  | next first rest ih => exact trans (event_next stable foreign first) ih

theorem linked_external (program : Events.Program E) (fn : External E)
    (internalFree : program.internal.definitions fn.signature.name = none)
    (externalFree : program.externals fn.signature.name = none)
    (previous : ProgramPreserves R program) (added : ExternalPreserves R fn) :
    ProgramPreserves R (Linkage.withExternal program fn internalFree externalFree) := by
  intro name target found
  by_cases same : name = fn.signature.name
  · simp only [Linkage.withExternal, if_pos same, Option.some.injEq] at found
    subst target
    exact added
  · exact previous name target (by simpa only [Linkage.withExternal, if_neg same] using found)

theorem linked_address (program : Events.Program E) (address : Address) (name : String)
    (available : program.addresses address = none)
    (external : ∃ fn, program.externals name = some fn)
    (previous : ProgramPreserves R program) :
    ProgramPreserves R (Linkage.withAddress program address name available external) := previous

/-- Every thread uses the current shared heap. This lifts the same per-call
invariant through arbitrary modeled interleavings; it does not prove race freedom. -/
theorem concurrent_next (stable : Stable R) (foreign : ProgramPreserves R program)
    (step : Concurrent.Step program before thread events after) : R before.heap after.heap := by
  cases step with
  | run found executed =>
    simpa only [Concurrent.heap_withHeap] using event_next stable foreign executed

theorem concurrent_reaches (stable : Stable R)
    (trans : ∀ {a b c}, R a b → R b c → R a c)
    (foreign : ProgramPreserves R program)
    (path : Transition.Reaches (fun a b => ∃ thread events, Concurrent.Step program a thread events b)
      before after) : R before.heap after.heap := by
  induction path with
  | refl => exact stable.refl _
  | next first rest ih =>
    obtain ⟨thread, events, step⟩ := first
    exact trans (concurrent_next stable foreign step) ih
end Rumoca.CStoreInvariant

namespace Rumoca.CStoreInvariant
open CTree CMemory CCalls CCalls.Events
variable [CInterface] {E : Type} {R : Heap → Heap → Prop}

/-- Any failure of a store-stable, transitive heap relation is witnessed by
an actual foreign execution in the path, with exact arguments and trace split.
No callback contract, successful termination or foreign determinism is assumed. -/
theorem foreign_change_origin (stable : Stable R)
    (trans : ∀ {a b c}, R a b → R b c → R a c)
    (path : Transition.Events.Reaches (Events.machine program).step s events t)
    (changed : ¬ R (CReadOnly.typedHeap s) (CReadOnly.typedHeap t)) :
    ∃ preEvents callEvents suffix name, ∃ fn : External E, ∃ args values before result after stack,
      Transition.Events.Reaches (Events.machine program).step s preEvents
        (.calling name args before stack) ∧
      program.externals name = some fn ∧
      convertedArguments fn.signature.parameters args = some values ∧
      fn.execute values before callEvents result after ∧ ¬ R before after ∧
      Transition.Events.Reaches (Events.machine program).step
        (.returning result after stack) suffix t ∧
      events = preEvents ++ callEvents ++ suffix := by
  induction path with
  | refl => exact False.elim (changed (stable.refl _))
  | @next s first middle rest t step path ih =>
    by_cases preserved : R (CReadOnly.typedHeap s) (CReadOnly.typedHeap middle)
    · have tailChanged : ¬ R (CReadOnly.typedHeap middle) (CReadOnly.typedHeap t) :=
        fun tail => changed (trans preserved tail)
      obtain ⟨preEvents, callEvents, suffix, name, fn, args, values, before, result, after, stack,
        entered, bound, converted, executed, altered, returns, trace⟩ := ih tailChanged
      exact ⟨first ++ preEvents, callEvents, suffix, name, fn, args, values, before, result, after, stack,
        .next step entered, bound, converted, executed, altered, returns,
        by simp only [trace, List.append_assoc]⟩
    · cases step with
      | internal step => exact False.elim (preserved (internal_next stable _ step))
      | @external name fn args values before callEvents result after stack bound converted executed =>
        exact ⟨[], first, rest, name, fn, args, values, before, result, after, stack,
          .refl _, bound, converted, executed, preserved, path, rfl⟩
end Rumoca.CStoreInvariant
