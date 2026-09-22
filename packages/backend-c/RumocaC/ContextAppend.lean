import RumocaC.ContextCalls
import RumocaC.TypedCallProofs

/-! Typed.Continuation transport for the shared expression-parametric scheduler.
The outer caller is arbitrary and need not be field-free. -/
noncomputable section
namespace Rumoca.CContextMachine
open CTree CMemory CLoops CCalls
variable [interface : CInterface]
variable (expressions : Expressions)

omit interface in
theorem enter_append (s : CLoops.State) (resultType : String) (stack outer : Typed.Continuation) :
    enter expressions s resultType (stack.append outer) = (enter expressions s resultType stack).map (fun t => t.append outer) := by
  cases s with
  | returned => rfl
  | running code env types heap =>
    cases code with
    | nil => by_cases h : resultType = "void" <;> simp [enter, Typed.enterCallWith, h, Typed.State.append]
    | cons stmt rest =>
      cases ho : CCalls.callOperand stmt with
      | none => simp [enter, Typed.enterCallWith, ho]
      | some operand =>
        obtain ⟨destination, name, args⟩ := operand
        simp only [enter, Typed.enterCallWith, ho, bind, Option.bind_some]
        by_cases hs : (env name).isSome || name = "isfinite"
        · simp only [if_pos hs, Option.map_none]
        · cases CCalls.argumentsWith expressions env heap args <;>
            simp only [if_neg hs, Option.bind_some, Option.bind_none, pure,
              Option.map_none, Option.map_some, Typed.State.append, Typed.Continuation.append]

theorem resume_append (value : Value) (heap : Heap) (destination : Destination) (rest : List Stmt)
    (env : CBody.Locals) (types : Types) (resultType : String) (stack outer : Typed.Continuation) :
    resume expressions value heap (.caller destination rest env types resultType (stack.append outer)) =
      (resume expressions value heap (.caller destination rest env types resultType stack)).map (fun t => t.append outer) := by
  cases destination with
  | discard => rfl
  | ret => cases h : returnCast resultType value <;> simp [resume, Typed.resumeWith, h, Typed.State.append]
  | declare type name =>
    by_cases hf : (env name).isSome
    · simp [resume, Typed.resumeWith, hf]
    · cases ht : interface.types type with
      | none => simp [resume, Typed.resumeWith, hf, ht]
      | some declared => cases hc : convert declared value <;> simp [resume, Typed.resumeWith, hf, ht, hc, Typed.State.append]
  | assign target =>
    cases target <;>
      simp only [resume, Typed.resumeWith, bind, pure, Option.map_bind, Function.comp_def, Option.map_some, Typed.State.append]

theorem append_step (p : Program) (s t : Typed.State) (outer : Typed.Continuation) (h : next expressions p s = some t) :
    Transition.Reaches (machine expressions p).step (s.append outer) (t.append outer) := by
  cases s with
  | halted => cases h
  | returning value heap stack =>
    cases stack with
    | done =>
      change some (.halted ⟨value, heap⟩) = some t at h
      cases h
      exact .refl _
    | caller destination rest env types resultType stack =>
      apply Transition.Reaches.next (t := t.append outer) ?_ (.refl _)
      change resume expressions value heap (.caller destination rest env types resultType (stack.append outer)) = _
      rw [resume_append]
      exact congrArg (Option.map (fun t => t.append outer)) h
  | calling name args heap stack =>
    apply Transition.Reaches.next (t := t.append outer) ?_ (.refl _)
    cases hd : p.definitions name with
    | none => simp [next, Typed.nextIn, hd, Typed.nextWithExpressions] at h
    | some d => cases d with
      | kernel fn =>
        cases he : kernelEntry fn args <;> simp [next, Typed.nextIn, hd, he, Typed.nextWithExpressions] at h
        cases h
        simp [machine, Typed.machineWith, Typed.State.append, Typed.nextIn, hd, he, Typed.nextWithExpressions]
      | tree fn =>
        cases ha : parameters fn.signature.parameters args with
        | none => simp [next, Typed.nextIn, hd, ha, Typed.nextWithExpressions] at h
        | some env =>
          cases ht : CLoops.Calls.parameterTypes fn.signature.parameters <;> simp [next, Typed.nextIn, hd, ha, ht, Typed.nextWithExpressions] at h
          cases h
          simp [machine, Typed.machineWith, Typed.State.append, Typed.nextIn, hd, ha, ht, Typed.nextWithExpressions]
  | kernel state heap stack =>
    apply Transition.Reaches.next (t := t.append outer) ?_ (.refl _)
    cases state with
    | returned x => cases h; rfl
    | entry fn x n =>
      cases he : CStatements.next p.kernel (.entry fn x n) <;> simp [next, Typed.nextIn, he, Typed.nextWithExpressions] at h
      cases h
      simp [machine, Typed.machineWith, Typed.State.append, Typed.nextIn, he, Typed.nextWithExpressions]
    | running code locals =>
      cases he : CStatements.next p.kernel (.running code locals) <;> simp [next, Typed.nextIn, he, Typed.nextWithExpressions] at h
      cases h
      simp [machine, Typed.machineWith, Typed.State.append, Typed.nextIn, he, Typed.nextWithExpressions]
  | body state resultType stack =>
    apply Transition.Reaches.next (t := t.append outer) ?_ (.refl _)
    cases state with
    | returned result =>
      cases hc : returnCast resultType result.value <;> simp [next, Typed.nextIn, hc, Typed.nextWithExpressions] at h
      cases h
      simp [machine, Typed.machineWith, Typed.State.append, Typed.nextIn, hc, Typed.nextWithExpressions]
    | running code env types heap =>
      cases hn : loopNext expressions (.running code env types heap) with
      | none =>
        simp only [next, Typed.nextIn, hn, Typed.nextWithExpressions] at h
        simp only [machine, Typed.machineWith, Typed.State.append, Typed.nextIn, hn, enter_append, h, Option.map_some, Typed.nextWithExpressions]
      | some following =>
        simp only [next, Typed.nextIn, hn, Option.some.injEq, Typed.nextWithExpressions] at h
        subst t
        simp only [machine, Typed.machineWith, Typed.State.append, Typed.nextIn, hn, Typed.nextWithExpressions]

theorem append_reaches (p : Program) (h : Transition.Reaches (machine expressions p).step s t) (outer : Typed.Continuation) :
    Transition.Reaches (machine expressions p).step (s.append outer) (t.append outer) := by
  induction h with
  | refl => exact .refl _
  | next hs _ ih => exact (append_step expressions p _ _ outer hs).trans ih


end Rumoca.CContextMachine
