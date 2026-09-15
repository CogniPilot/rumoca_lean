import RumocaC.TypedCallProofs
import RumocaC.CallEvents
import RumocaC.CallIntervals
import RumocaC.CallDepth

namespace Rumoca.CCalls.Context
open CTree CMemory Typed

/-- Before a inner invocation returns to its suspended caller, its own root
return and final observation cannot yet be consumed. -/
def Active (state : Typed.State) : Prop :=
  ¬ Concurrent.Exit .done state ∧ (∀ result, state ≠ .halted result)

theorem depth_append (inner outer : Typed.Continuation) :
    CCallDepth.depth (inner.append outer) = CCallDepth.depth inner + CCallDepth.depth outer := by
  induction inner with
  | done => simp [Typed.Continuation.append, CCallDepth.depth]
  | caller destination rest env types resultType next ih =>
    simp only [Typed.Continuation.append, CCallDepth.depth, ih]
    omega

theorem append_eq_outer (inner outer : Typed.Continuation) : inner.append outer = outer ↔ inner = .done := by
  constructor
  · intro same
    have lengths := congrArg CCallDepth.depth same
    rw [depth_append] at lengths
    have zero : CCallDepth.depth inner = 0 := by omega
    cases inner with
    | done => rfl
    | caller => simp [CCallDepth.depth] at zero
  · rintro rfl
    rfl

theorem heap_append (state : Typed.State) (outer : Typed.Continuation) (heap : Heap) :
    Concurrent.withHeap (state.append outer) heap = (Concurrent.withHeap state heap).append outer := by
  cases state with
  | body state => cases state <;> rfl
  | _ => rfl

theorem active_of_suspended (state : Typed.State) (outer : Typed.Continuation)
    (active : ¬ Concurrent.Exit outer (state.append outer)) : Active state := by
  constructor
  · rintro ⟨value, heap, rfl⟩
    exact active ⟨value, heap, rfl⟩
  · rintro result rfl
    exact active ⟨result.value, result.heap, rfl⟩

theorem returned_local (state : Typed.State) (outer : Typed.Continuation)
    (running : ∀ result, state ≠ .halted result)
    (same : state.append outer = .returning value heap outer) :
    state = .returning value heap .done := by
  cases state with
  | returning result memory stack =>
    obtain ⟨rfl, rfl, appended⟩ := Typed.State.returning.inj same
    cases (append_eq_outer stack outer).mp appended
    rfl
  | halted result => exact False.elim (running result rfl)
  | _ => contradiction

variable [interface : CInterface] {E : Type}

theorem enter_append (program : Events.Program E) (state : CLoops.State)
    (resultType : String) (stack outer : Typed.Continuation) :
    Events.enterCall program state resultType (stack.append outer) =
      (Events.enterCall program state resultType stack).map (fun next => next.append outer) := by
  cases state with
  | returned result => rfl
  | running code env types heap =>
    cases code with
    | nil => by_cases void : resultType = "void" <;> simp [Events.enterCall, void, Typed.State.append]
    | cons stmt rest =>
      simp only [Events.enterCall, bind, pure, Option.map_bind, Function.comp_def,
        Option.map_some, Typed.State.append, Typed.Continuation.append]

/-- Context extension is an exact one-step equation before the inner root
returns. It reuses the authored body's evaluator and original function table. -/
theorem internal_append (program : Events.Program E) (state : Typed.State) (outer : Typed.Continuation)
    (active : Active state) :
    Events.internalNext program (state.append outer) =
      (Events.internalNext program state).map (fun next => next.append outer) := by
  cases state with
  | halted result => exact False.elim (active.2 result rfl)
  | returning value heap stack =>
    cases stack with
    | done => exact False.elim (active.1 ⟨value, heap, rfl⟩)
    | caller destination rest env types resultType stack =>
      exact Typed.resume_append value heap destination rest env types resultType stack outer
  | body state resultType stack =>
    cases state with
    | returned result =>
      simp [Events.internalNext, Typed.State.append, Typed.nextWith, Option.map_bind]
    | running code env types heap =>
      cases next : CLoops.next (.running code env types heap) <;>
        simp [Events.internalNext, Typed.State.append, Typed.nextWith, next, enter_append]
  | calling name args heap stack =>
    cases defined : program.internal.definitions name with
    | none => simp [Events.internalNext, Typed.State.append, Typed.nextWith, defined]
    | some fn =>
      cases fn with
      | tree fn =>
        simp [Events.internalNext, Typed.State.append, Typed.nextWith, defined, Option.map_bind]
      | kernel fn =>
        simp [Events.internalNext, Typed.State.append, Typed.nextWith, defined, Option.map_bind]
  | kernel state heap stack =>
    cases state <;> simp [Events.internalNext, Typed.State.append, Typed.nextWith, Option.map_bind]

private theorem internal_unappend (program : Events.Program E) (state : Typed.State)
    (outer : Typed.Continuation) (active : Active state)
    (step : Events.internalNext program (state.append outer) = some after) :
    ∃ next, Events.Step program state [] next ∧ next.append outer = after := by
  rw [internal_append program state outer active] at step
  obtain ⟨next, moved, same⟩ := Option.map_eq_some_iff.mp step
  exact ⟨next, .internal moved, same⟩

/-- An actual contextual C step supplies a matching inner step, including
its exact foreign events and output heap. No inner execution is assumed. -/
theorem step_unappend (program : Events.Program E) (state : Typed.State) (outer : Typed.Continuation)
    (active : Active state) (step : Events.Step program (state.append outer) events after) :
    ∃ next, Events.Step program state events next ∧ next.append outer = after := by
  cases state with
  | body state resultType stack =>
    cases step with
    | internal moved => exact internal_unappend program _ outer active moved
  | kernel state heap stack =>
    cases step with
    | internal moved => exact internal_unappend program _ outer active moved
  | returning value heap stack =>
    cases step with
    | internal moved => exact internal_unappend program _ outer active moved
  | halted result => exact False.elim (active.2 result rfl)
  | calling name args heap stack =>
    cases step with
    | internal moved => exact internal_unappend program _ outer active moved
    | external found converted executed => exact ⟨_, .external found converted executed, rfl⟩


/-- The converse direction preserves the exact event list, not merely a
terminating behavior or an unlabelled reachability relation. -/
theorem step_append (program : Events.Program E) (state : Typed.State) (outer : Typed.Continuation)
    (active : Active state) (step : Events.Step program state events after) :
    Events.Step program (state.append outer) events (after.append outer) := by
  cases step with
  | internal moved =>
    apply Events.Step.internal
    rw [internal_append program state outer active, moved]
    rfl
  | external found converted executed => exact .external found converted executed

omit interface in
theorem appended_heap (state : Typed.State) (outer : Typed.Continuation) :
    CReadOnly.typedHeap (state.append outer) = CReadOnly.typedHeap state := by
  cases state with
  | body state => cases state <;> rfl
  | _ => rfl

end Rumoca.CCalls.Context
