import RumocaC.CallContextHistory

namespace Rumoca.CCalls.Context
open CTree CMemory

def Live (state : Typed.State) : Prop := ∀ result, state ≠ .halted result

theorem live_heap (live : Live state) (heap : Heap) : Live (Concurrent.withHeap state heap) := by
  cases state with
  | body state => cases state <;> simp [Live, Concurrent.withHeap]
  | halted result => exact False.elim (live result rfl)
  | _ => simp [Live, Concurrent.withHeap]

variable [CInterface] {E : Type}

/-- An actual inner step cannot halt before returning to its own root.
This is independent of function bodies and foreign event outcomes. -/
theorem step_live (program : Events.Program E) (active : Active before)
    (step : Events.Step program before events after) : Live after := by
  intro result same
  subst after
  cases step with
  | internal moved =>
    cases before with
    | halted result => simp [Events.internalNextWith, Typed.nextWithExpressions] at moved
    | returning value heap stack =>
      cases stack with
      | done => exact active.1 ⟨value, heap, rfl⟩
      | caller destination rest env types resultType stack =>
        cases destination <;>
          simp_all [Events.internalNextWith, Typed.nextWithExpressions, Typed.resumeWith,
            Option.bind_eq_some_iff]
        split at moved <;> simp_all [Option.bind_eq_some_iff]
    | body state resultType stack =>
      cases state with
      | returned value => simp [Events.internalNextWith, Typed.nextWithExpressions, Option.bind_eq_some_iff] at moved
      | running code env types heap =>
        cases next : CLoops.next (.running code env types heap) with
        | some following => simp [Events.internalNextWith, Typed.nextWithExpressions, next] at moved
        | none =>
          cases code <;> simp [Events.internalNextWith, Typed.nextWithExpressions, next,
            Events.enterCallWith, Option.bind_eq_some_iff] at moved
    | calling name args heap stack =>
      simp only [Events.internalNextWith, Typed.nextWithExpressions, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at moved
      obtain ⟨fn, _, entered⟩ := moved
      cases fn <;> simp [Option.bind_eq_some_iff] at entered
    | kernel state heap stack =>
      cases state <;> simp [Events.internalNextWith, Typed.nextWithExpressions, Option.bind_eq_some_iff] at moved

/-- A local invariant can be followed beneath an arbitrary saved caller up
to its exact return boundary. No replacement call interpreter is involved. -/
def Suspended (P : Typed.State → Prop) (outer : Typed.Continuation) (state : Typed.State) : Prop :=
  ∃ inner, state = inner.append outer ∧ P inner ∧ Live inner

omit [CInterface] in
theorem suspended_heap (ready : Suspended P outer state) (heap : Heap)
    (stable : ∀ state, P state → ∀ heap, P (Concurrent.withHeap state heap)) :
    Suspended P outer (Concurrent.withHeap state heap) := by
  obtain ⟨inner, rfl, ready, live⟩ := ready
  exact ⟨Concurrent.withHeap inner heap, heap_append inner outer heap, stable inner ready heap, live_heap live heap⟩

theorem suspended_step (program : Events.Program E)
    (preserves : ∀ before events after, P before → Events.Step program before events after → P after)
    (ready : Suspended P outer before) (active : ¬ Concurrent.Exit outer before)
    (step : Events.Step program before events after) : Suspended P outer after := by
  obtain ⟨inner, rfl, ready, _⟩ := ready
  have active := active_of_suspended inner outer active
  obtain ⟨next, moved, rfl⟩ := step_unappend program inner outer active step
  exact ⟨next, rfl, preserves _ _ _ ready moved, step_live program active moved⟩

omit [CInterface] in
theorem suspended_call (ready : Suspended P outer (.calling name args heap stack)) :
    ∃ innerStack, stack = innerStack.append outer ∧ P (.calling name args heap innerStack) := by
  obtain ⟨inner, same, ready, _⟩ := ready
  cases inner with
  | calling function values memory innerStack =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := Typed.State.calling.inj same
    exact ⟨innerStack, rfl, ready⟩
  | _ => contradiction

end Rumoca.CCalls.Context
