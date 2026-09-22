import RumocaC.FieldFreeLoop
import RumocaC.TypedCallProofs

/-! Transfer of ordinary numerical helper executions into the array-aware
typed scheduler. Only numerical frames are field-free; public callers need not be. -/
noncomputable section
namespace Rumoca.CContextMachine.FieldFree
open CTree CMemory CCalls CDeclaredMembers.FieldFree
variable [interface : CInterface]

def Frames : CLoops.Calls.Continuation → Prop
  | .done => True
  | .caller rest _ _ outer => AdmittedBody rest ∧ Frames outer

def Ready : CLoops.Calls.State → Prop
  | .body state stack => LoopFree state ∧ Frames stack
  | .calling _ _ _ stack | .returning _ stack => Frames stack
  | .halted _ => True

def DefinitionsFree (definitions : CLoops.Calls.Definitions) : Prop :=
  ∀ name fn, definitions name = some fn → AdmittedBody fn.body

theorem enter_ready (ready : Ready (.body state stack))
    (step : CLoops.Calls.enterCall state stack = some after) : Ready after := by
  obtain ⟨code, frames⟩ := ready
  unfold CLoops.Calls.enterCall CLoops.Calls.enterCallWith at step
  split at step
  · rename_i name args rest env types heap
    have tail : AdmittedBody rest := by
      have parts := code
      change body (_ :: rest) = true at parts
      rw [body_cons, Bool.and_eq_true] at parts
      exact parts.2
    split at step
    · cases step
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at step
      obtain ⟨values, _, step⟩ := step
      cases step
      exact ⟨tail, frames⟩
  · cases step

theorem ready_next (admitted : DefinitionsFree definitions) (ready : Ready before)
    (step : CLoops.Calls.next definitions before = some after) : Ready after := by
  cases before with
  | halted => cases step
  | returning heap stack =>
    cases stack <;> simp only [CLoops.Calls.next, CLoops.Calls.nextWith, Option.some.injEq] at step <;> subst after
    · trivial
    · exact ready
  | calling name args heap stack =>
    simp only [CLoops.Calls.next, CLoops.Calls.nextWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at step
    obtain ⟨fn, found, step⟩ := step
    split at step
    · cases step
    · simp only [Option.bind_eq_some_iff, Option.pure_def] at step
      obtain ⟨env, _, types, _, step⟩ := step
      cases step
      exact ⟨admitted name fn found, ready⟩
  | body state stack =>
    cases state with
    | returned result =>
      simp only [CLoops.Calls.next, CLoops.Calls.nextWith] at step
      split at step
      · cases step; exact ready.2
      · cases step
    | running code env types heap =>
      cases ordinary : CLoops.next (.running code env types heap) with
      | some following =>
        simp only [CLoops.Calls.next, CLoops.Calls.nextWith, ordinary, Option.some.injEq] at step
        subst after
        exact ⟨loop_free_next ready.1 ordinary, ready.2⟩
      | none =>
        simp only [CLoops.Calls.next, CLoops.Calls.nextWith, ordinary] at step
        exact enter_ready ready step

theorem ready_reaches (admitted : DefinitionsFree definitions) (ready : Ready before)
    (ran : Transition.Reaches (CLoops.Calls.machine definitions).step before after) : Ready after := by
  induction ran with
  | refl => exact ready
  | next step _ ih => exact ih (ready_next admitted ready step)

theorem enter_loop_context (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (state : CLoops.State)
    (stack : CLoops.Calls.Continuation) (after : CLoops.Calls.State)
    (free : LoopFree state) (step : CLoops.Calls.enterCall state stack = some after) :
    enter (declared declarations objects) state "void" (Typed.loopContinuation stack) =
      some (Typed.loopState after) := by
  unfold CLoops.Calls.enterCall CLoops.Calls.enterCallWith at step
  split at step
  · rename_i name args rest env types heap
    have head := body_member free (.eval (.call (.id name) args)) List.mem_cons_self
    have argsFree : args.all expression = true := by
      simpa [statement, CDeclaredMembers.FieldFree.expressions, expression, argumentList_all] using head
    have values := arguments_agreement declarations objects env heap args argsFree
    simp only [enter, Typed.enterCallWith, CCalls.callOperand, bind, Option.bind_some, values]
    by_cases shadowed : (env name).isSome || name = "isfinite"
    · simp only [if_pos shadowed] at step
      cases step
    · rw [if_neg shadowed] at step ⊢
      cases ha : CCalls.argumentsWith CBody.legacyExpressions env heap args with
      | none => simp [ha] at step
      | some values =>
        simp only [ha, bind, Option.bind_some, pure] at step ⊢
        cases step
        rfl
  · cases step

theorem loop_step_context (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program)
    (definitions : CLoops.Calls.Definitions) (linked : Typed.Extends definitions p)
    (s t : CLoops.Calls.State) (ready : Ready s)
    (step : CLoops.Calls.next definitions s = some t) :
    next (declared declarations objects) p (Typed.loopState s) = some (Typed.loopState t) := by
  have old := Typed.loop_step p definitions linked s t step
  cases s with
  | halted => cases step
  | calling => exact old
  | returning heap stack => cases stack <;> exact old
  | body state stack =>
    cases state with
    | returned => exact old
    | running code env types heap =>
      have same := loop_next_agreement declarations objects (.running code env types heap) ready.1
      cases following : CLoops.next (.running code env types heap) with
      | some after =>
        simpa only [Typed.loopState, Typed.next, Typed.nextIn, Typed.nextWithExpressions, following,
          next, Typed.nextIn, Typed.nextWithExpressions, same] using old
      | none =>
        have called : CLoops.Calls.enterCall (.running code env types heap) stack = some t := by
          simpa only [CLoops.Calls.next, CLoops.Calls.nextWith, following] using step
        simpa only [Typed.loopState, next, Typed.nextIn, Typed.nextWithExpressions, same, following] using
          enter_loop_context declarations objects (.running code env types heap) stack t ready.1 called

theorem loop_reaches_context (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program)
    (definitions : CLoops.Calls.Definitions) (linked : Typed.Extends definitions p)
    (admitted : DefinitionsFree definitions) (ready : Ready s)
    (ran : Transition.Reaches (CLoops.Calls.machine definitions).step s t) :
    Transition.Reaches (machine (declared declarations objects) p).step
      (Typed.loopState s) (Typed.loopState t) := by
  induction ran with
  | refl => exact .refl _
  | next step _ ih =>
    exact .next (loop_step_context declarations objects p definitions linked _ _ ready step)
      (ih (ready_next admitted ready step))

end Rumoca.CContextMachine.FieldFree
