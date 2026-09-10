import RumocaC.TypedCalls

/-! Successful tensor executions embed step by step into typed calls.
Appending a caller to a closed run uses a stuttering step only at the old
terminal state. Thus a proved finite tensor call resumes any ordinary caller
with the same saved locals/types and the proved heap effects. This is not a
simulation of every old FMI body; those body proofs must be connected
separately under the typed statement machine's scope rules. -/
noncomputable section
namespace Rumoca.CCalls.Typed
open CTree CMemory CLoops
variable [interface : CInterface]

def loopContinuation : CLoops.Calls.Continuation → Continuation
  | .done => .done
  | .caller rest locals types outer => .caller .discard rest locals types "void" (loopContinuation outer)

def loopState : CLoops.Calls.State → State
  | .body state stack => .body state "void" (loopContinuation stack)
  | .calling name args heap stack => .calling name args heap (loopContinuation stack)
  | .returning heap stack => .returning .void heap (loopContinuation stack)
  | .halted heap => .halted ⟨.void, heap⟩

def Extends (definitions : CLoops.Calls.Definitions) (p : Program) : Prop :=
  ∀ name fn, definitions name = some fn → p.definitions name = some (.tree fn)

theorem enter_loop_call (s : CLoops.State) (stack : CLoops.Calls.Continuation) (t : CLoops.Calls.State)
    (h : CLoops.Calls.enterCall s stack = some t) :
    enterCall s "void" (loopContinuation stack) = some (loopState t) := by
  unfold CLoops.Calls.enterCall at h
  split at h
  · rename_i name args rest env types heap
    simp only [enterCall, CCalls.callOperand, bind, Option.bind_some]
    by_cases shadowed : (env name).isSome || name = "isfinite"
    · simp only [if_pos shadowed] at h
      cases h
    · rw [if_neg shadowed] at h ⊢
      cases ha : CCalls.arguments env heap args with
      | none => simp [ha] at h
      | some values =>
        simp only [ha, bind, Option.bind_some, pure] at h ⊢
        cases h
        rfl
  · cases h

theorem loop_step (p : Program) (definitions : CLoops.Calls.Definitions) (linked : Extends definitions p)
    (s t : CLoops.Calls.State) (h : CLoops.Calls.next definitions s = some t) :
    next p (loopState s) = some (loopState t) := by
  cases s with
  | halted => cases h
  | returning heap stack =>
    cases stack <;> simp only [CLoops.Calls.next, Option.some.injEq] at h <;> subst t <;> rfl
  | body state stack =>
    cases state with
    | returned result =>
      simp only [CLoops.Calls.next] at h
      by_cases void : result.value = .void
      · rw [if_pos void] at h
        cases h
        simp only [loopState, next, returnCast, ↓reduceIte, void, bind, Option.bind_some, pure]
      · rw [if_neg void] at h
        cases h
    | running code locals types heap =>
      cases hn : CLoops.next (.running code locals types heap) with
      | none =>
        simp only [CLoops.Calls.next, hn] at h
        simpa only [loopState, next, hn] using enter_loop_call _ stack t h
      | some following =>
        simp only [CLoops.Calls.next, hn, Option.some.injEq] at h
        subst t
        simp only [loopState, next, hn]
  | calling name args heap stack =>
    cases hd : definitions name with
    | none => simp [CLoops.Calls.next, hd] at h
    | some fn =>
      have hp := linked name fn hd
      simp only [CLoops.Calls.next, hd, bind, Option.bind_some] at h
      by_cases void : fn.signature.result = "void"
      · rw [if_neg (not_not_intro void)] at h
        cases ha : parameters fn.signature.parameters args with
        | none => simp [ha] at h
        | some locals =>
          cases ht : CLoops.Calls.parameterTypes fn.signature.parameters with
          | none => simp [ha, ht] at h
          | some types =>
            simp only [ha, ht, Option.bind_some, pure] at h
            cases h
            simp only [loopState, next, hp, ha, ht, void, bind, Option.bind_some, pure]
      · rw [if_pos void] at h
        cases h

theorem loop_reaches (p : Program) (definitions : CLoops.Calls.Definitions) (linked : Extends definitions p)
    (h : Transition.Reaches (CLoops.Calls.machine definitions).step s t) :
    Transition.Reaches (machine p).step (loopState s) (loopState t) := by
  induction h with
  | refl => exact .refl _
  | next hs _ ih => exact .next (loop_step p definitions linked _ _ hs) ih

theorem loop_behaviors (p : Program) (definitions : CLoops.Calls.Definitions) (linked : Extends definitions p)
    (h : Transition.Reaches (CLoops.Calls.machine definitions).step s (.halted heap)) (behavior) :
    (machine p).Behaves (loopState s) behavior ↔ behavior = .terminates ⟨.void, heap⟩ :=
  (machine p).behavior_iff (loop_reaches p definitions linked h) rfl


def Continuation.append : Continuation → Continuation → Continuation
  | .done, outer => outer
  | .caller destination rest env types resultType next, outer =>
      .caller destination rest env types resultType (next.append outer)

def State.append : State → Continuation → State
  | .body state resultType stack, outer => .body state resultType (stack.append outer)
  | .calling name args heap stack, outer => .calling name args heap (stack.append outer)
  | .kernel state heap stack, outer => .kernel state heap (stack.append outer)
  | .returning value heap stack, outer => .returning value heap (stack.append outer)
  | .halted result, outer => .returning result.value result.heap outer

theorem enter_append (s : CLoops.State) (resultType : String) (stack outer : Continuation) :
    enterCall s resultType (stack.append outer) = (enterCall s resultType stack).map (fun t => t.append outer) := by
  cases s with
  | returned => rfl
  | running code env types heap =>
    cases code with
    | nil => by_cases h : resultType = "void" <;> simp [enterCall, h, State.append]
    | cons stmt rest =>
      cases ho : CCalls.callOperand stmt with
      | none => simp [enterCall, ho]
      | some operand =>
        obtain ⟨destination, name, args⟩ := operand
        simp only [enterCall, ho, bind, Option.bind_some]
        by_cases hs : (env name).isSome || name = "isfinite"
        · simp only [if_pos hs, Option.map_none]
        · cases CCalls.arguments env heap args <;>
            simp only [if_neg hs, Option.bind_some, Option.bind_none, pure,
              Option.map_none, Option.map_some, State.append, Continuation.append]

theorem resume_append (value : Value) (heap : Heap) (destination : Destination) (rest : List Stmt)
    (env : CBody.Locals) (types : Types) (resultType : String) (stack outer : Continuation) :
    resume value heap (.caller destination rest env types resultType (stack.append outer)) =
      (resume value heap (.caller destination rest env types resultType stack)).map (fun t => t.append outer) := by
  cases destination with
  | discard => rfl
  | ret => cases h : returnCast resultType value <;> simp [resume, h, State.append]
  | declare type name =>
    by_cases hf : (env name).isSome
    · simp [resume, hf]
    · cases ht : interface.types type with
      | none => simp [resume, hf, ht]
      | some declared => cases hc : convert declared value <;> simp [resume, hf, ht, hc, State.append]
  | assign target =>
    cases target <;>
      simp only [resume, bind, pure, Option.map_bind, Function.comp_def, Option.map_some, State.append]

theorem append_step (p : Program) (s t : State) (outer : Continuation) (h : next p s = some t) :
    Transition.Reaches (machine p).step (s.append outer) (t.append outer) := by
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
      change resume value heap (.caller destination rest env types resultType (stack.append outer)) = _
      rw [resume_append]
      exact congrArg (Option.map (fun t => t.append outer)) h
  | calling name args heap stack =>
    apply Transition.Reaches.next (t := t.append outer) ?_ (.refl _)
    cases hd : p.definitions name with
    | none => simp [next, hd] at h
    | some d => cases d with
      | kernel fn =>
        cases he : kernelEntry fn args <;> simp [next, hd, he] at h
        cases h
        simp [machine, State.append, next, hd, he]
      | tree fn =>
        cases ha : parameters fn.signature.parameters args with
        | none => simp [next, hd, ha] at h
        | some env =>
          cases ht : CLoops.Calls.parameterTypes fn.signature.parameters <;> simp [next, hd, ha, ht] at h
          cases h
          simp [machine, State.append, next, hd, ha, ht]
  | kernel state heap stack =>
    apply Transition.Reaches.next (t := t.append outer) ?_ (.refl _)
    cases state with
    | returned x => cases h; rfl
    | entry fn x n =>
      cases he : CStatements.next p.kernel (.entry fn x n) <;> simp [next, he] at h
      cases h
      simp [machine, State.append, next, he]
    | running code locals =>
      cases he : CStatements.next p.kernel (.running code locals) <;> simp [next, he] at h
      cases h
      simp [machine, State.append, next, he]
  | body state resultType stack =>
    apply Transition.Reaches.next (t := t.append outer) ?_ (.refl _)
    cases state with
    | returned result =>
      cases hc : returnCast resultType result.value <;> simp [next, hc] at h
      cases h
      simp [machine, State.append, next, hc]
    | running code env types heap =>
      cases hn : CLoops.next (.running code env types heap) with
      | none =>
        simp only [next, hn] at h
        simp only [machine, State.append, next, hn, enter_append, h, Option.map_some]
      | some following =>
        simp only [next, hn, Option.some.injEq] at h
        subst t
        simp only [machine, State.append, next, hn]

theorem append_reaches (p : Program) (h : Transition.Reaches (machine p).step s t) (outer : Continuation) :
    Transition.Reaches (machine p).step (s.append outer) (t.append outer) := by
  induction h with
  | refl => exact .refl _
  | next hs _ ih => exact (append_step p _ _ outer hs).trans ih

theorem loop_call_reaches (p : Program) (definitions : CLoops.Calls.Definitions) (linked : Extends definitions p)
    (h : Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling name args heap .done) (.returning finalHeap .done)) (outer : Continuation) :
    Transition.Reaches (machine p).step (.calling name args heap outer) (.returning .void finalHeap outer) := by
  have complete := h.trans (Transition.Reaches.next (by rfl) (.refl (.halted finalHeap)))
  exact append_reaches p (loop_reaches p definitions linked complete) outer


theorem body_step (p : Program) (h : CLoops.next s = some t) (type stack) :
    next p (.body s type stack) = some (.body t type stack) := by
  cases s with
  | returned => simp [CLoops.next] at h
  | running => simp [next, h]

theorem body_reaches (p : Program)
    (h : Transition.Reaches CLoops.machine.step s t) (type stack) :
    Transition.Reaches (machine p).step (.body s type stack) (.body t type stack) := by
  induction h with
  | refl => exact .refl _
  | next hs _ ih => exact .next (body_step p hs type stack) ih

theorem kernel_step (p : Program) (h : CStatements.next p.kernel s = some t) (heap stack) :
    next p (.kernel s heap stack) = some (.kernel t heap stack) := by
  cases s <;> simp_all [CStatements.next, next]

theorem kernel_reaches (p : Program) (h : CStatements.Reaches p.kernel s t) (heap stack) :
    Transition.Reaches (machine p).step (.kernel s heap stack) (.kernel t heap stack) := by
  induction h with
  | refl => exact .refl _
  | next hs _ ih => exact .next (kernel_step p hs heap stack) ih

theorem tree_entry (p : Program) (name args heap stack fn env types)
    (hd : p.definitions name = some (.tree fn))
    (hp : parameters fn.signature.parameters args = some env)
    (ht : CLoops.Calls.parameterTypes fn.signature.parameters = some types) :
    next p (.calling name args heap stack) =
      some (.body (.running fn.body env types heap) fn.signature.result stack) := by
  simp [next, hd, hp, ht]

theorem loop_terminates_reaches (p : Program) (definitions : CLoops.Calls.Definitions)
    (linked : Extends definitions p)
    (h : (CLoops.Calls.machine definitions).Behaves s (.terminates finalHeap)) :
    Transition.Reaches (machine p).step (loopState s) (.halted ⟨.void, finalHeap⟩) := by
  cases h with
  | terminates ran final =>
    rename_i t
    cases t <;> simp [CLoops.Calls.machine] at final
    cases final
    exact loop_reaches p definitions linked ran

theorem loop_terminates_context (p : Program) (definitions : CLoops.Calls.Definitions)
    (linked : Extends definitions p)
    (h : (CLoops.Calls.machine definitions).Behaves (.calling name args heap .done) (.terminates finalHeap))
    (outer : Continuation) :
    Transition.Reaches (machine p).step (.calling name args heap outer) (.returning .void finalHeap outer) :=
  append_reaches p (loop_terminates_reaches p definitions linked h) outer

/-- A complete call can be used under any saved caller and has exactly one
observable outcome when invoked on its own. -/
def CallResult (p : Program) (name : String) (args : List Value) (heap finalHeap : Heap) : Prop :=
  (∀ stack, Transition.Reaches (machine p).step
    (.calling name args heap stack) (.returning .void finalHeap stack)) ∧
  ∀ behavior, (machine p).Behaves (.calling name args heap .done) behavior ↔
    behavior = .terminates ⟨.void, finalHeap⟩

theorem loop_call_result (p : Program) (definitions : CLoops.Calls.Definitions)
    (linked : Extends definitions p)
    (h : (CLoops.Calls.machine definitions).Behaves (.calling name args heap .done) (.terminates finalHeap)) :
    CallResult p name args heap finalHeap :=
  ⟨loop_terminates_context p definitions linked h,
    fun _ => (machine p).behavior_iff (loop_terminates_reaches p definitions linked h) rfl⟩

theorem invoke_step (p : Program) (name : String) (args : List Expr) (values : List Value)
    (rest : List Stmt) (env : CBody.Locals) (types : Types) (heap : Heap) (type : String) (stack : Continuation)
    (ordinary : name ≠ "isfinite") (unshadowed : env name = none)
    (evaluated : arguments env heap args = some values) :
    next p (.body (.running (.eval (.call (.id name) args) :: rest) env types heap) type stack) =
      some (.calling name values heap (.caller .discard rest env types type stack)) := by
  have pureCall : CBody.eval env heap (.call (.id name) args) = none := by
    simp [CBody.eval, ordinary]
  simp only [next, CLoops.next, CLoops.eval, pureCall, bind, Option.bind_none,
    enterCall, callOperand, Option.bind_some, unshadowed, Option.isSome_none,
    Bool.false_or, decide_eq_true_eq, if_neg ordinary, evaluated, pure]

theorem invoke_reaches (p : Program) (h : CallResult p name values heap finalHeap)
    (args : List Expr) (rest : List Stmt) (env : CBody.Locals) (types : Types)
    (type : String) (stack : Continuation) (ordinary : name ≠ "isfinite") (unshadowed : env name = none)
    (evaluated : arguments env heap args = some values) :
    Transition.Reaches (machine p).step
      (.body (.running (.eval (.call (.id name) args) :: rest) env types heap) type stack)
      (.body (.running rest env types finalHeap) type stack) := by
  exact .next (invoke_step p name args values rest env types heap type stack ordinary unshadowed evaluated)
    ((h.1 _).trans (.next rfl (.refl _)))

theorem invoke_return_reaches (p : Program) (h : CallResult p name values heap finalHeap)
    (args : List Expr) (status : Expr) (env : CBody.Locals) (types : Types)
    (type : String) (stack : Continuation) (ordinary : name ≠ "isfinite") (unshadowed : env name = none)
    (evaluated : arguments env heap args = some values)
    (statusValue returnedValue : Value) (statusEval : CLoops.eval env types finalHeap status = some statusValue)
    (converted : returnCast type statusValue = some returnedValue) :
    Transition.Reaches (machine p).step
      (.body (.running [.eval (.call (.id name) args), .ret (some status)] env types heap) type stack)
      (.returning returnedValue finalHeap stack) := by
  apply (invoke_reaches p h args [.ret (some status)] env types type stack
    ordinary unshadowed evaluated).trans
  refine .next (t := .body (.returned ⟨statusValue, finalHeap⟩) type stack) ?_ ?_
  · exact body_step p (by simp [CLoops.next, statusEval]) type stack
  · exact .next (by simp [machine, next, converted]) (.refl _)


end Rumoca.CCalls.Typed
