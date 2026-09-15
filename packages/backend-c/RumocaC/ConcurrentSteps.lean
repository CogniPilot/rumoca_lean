import RumocaC.ConcurrentCalls

/-! Exact selected scheduler steps, retaining the current shared heap and saved continuations. -/
noncomputable section
namespace Rumoca.CCalls.Concurrent
open CTree CMemory
variable [CInterface] {E : Type} {program : Events.Program E}

/-- A selected foreign call uses the current shared heap. This characterizes
every next scheduler step without assuming a whole call has completed. -/
theorem external_step_iff (selected : before.threads thread = some saved)
    (atCall : withHeap saved before.heap = .calling name args before.heap stack)
    (bound : program.externals name = some fn)
    (converted : Events.convertedArguments fn.signature.parameters args = some values) :
    Step program before thread events after ↔
      ∃ result heap, fn.execute values before.heap events result heap ∧
        after = ⟨heap, update before.threads thread (.returning result heap stack)⟩ := by
  constructor
  · intro step
    cases step with
    | run found executed =>
      have same := Option.some.inj (found.symm.trans selected)
      cases same
      rw [atCall] at executed
      cases executed with
      | internal next =>
        rw [Events.external_entry_exclusive program bound] at next
        contradiction
      | external found converted' executed =>
        cases Option.some.inj (found.symm.trans bound)
        cases Option.some.inj (converted'.symm.trans converted)
        exact ⟨_, _, executed, rfl⟩
  · rintro ⟨result, heap, executed, rfl⟩
    exact .run selected (by rw [atCall]; exact .external bound converted executed)

/-- Internal computation is silent and has a unique next shared scheduler
state. Other threads may have changed the heap since this control was saved. -/
theorem internal_step_iff (selected : before.threads thread = some saved)
    (next : Events.internalNext program (withHeap saved before.heap) = some result) :
    Step program before thread events after ↔
      events = [] ∧ after = ⟨CReadOnly.typedHeap result, update before.threads thread result⟩ := by
  constructor
  · intro step
    cases step with
    | run found executed =>
      have same := Option.some.inj (found.symm.trans selected)
      cases same
      obtain ⟨rfl, rfl⟩ := Events.internal_unique program next _ _ executed
      exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .run selected (.internal next)
end Rumoca.CCalls.Concurrent

namespace Rumoca.CCalls.Concurrent
open CTree CMemory
variable [CInterface] {E : Type} {program : Events.Program E}

/-- Recover conversion and the foreign effect from an actual selected step.
No converted-value shape is supplied as a premise. -/
theorem external_step_values_iff (selected : before.threads thread = some saved)
    (atCall : withHeap saved before.heap = .calling name args before.heap stack)
    (bound : program.externals name = some fn) :
    Step program before thread events after ↔
      ∃ values result heap,
        Events.convertedArguments fn.signature.parameters args = some values ∧
        fn.execute values before.heap events result heap ∧
        after = ⟨heap, update before.threads thread (.returning result heap stack)⟩ := by
  constructor
  · intro step
    cases step with
    | run found executed =>
      cases Option.some.inj (found.symm.trans selected)
      rw [atCall] at executed
      cases executed with
      | internal next =>
        rw [Events.external_entry_exclusive program bound] at next
        contradiction
      | external found converted executed =>
        cases Option.some.inj (found.symm.trans bound)
        exact ⟨_, _, _, converted, executed, rfl⟩
  · rintro ⟨values, result, heap, converted, executed, rfl⟩
    exact .run selected (by rw [atCall]; exact .external bound converted executed)

end Rumoca.CCalls.Concurrent
