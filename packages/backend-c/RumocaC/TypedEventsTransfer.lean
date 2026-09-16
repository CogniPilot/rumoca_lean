import RumocaC.TypedCallProofs
import RumocaC.CallEvents

/-! Transfer of a completed void loop-call execution from the typed tensor call
scheduler into the observable call machine.

Both machines are the same `CCalls.Typed.nextWith` scheduler over the same
program definitions; they differ only in the call-site `enterCall`. The typed
scheduler reads a direct callee name from the statement, while the observable
scheduler resolves the callee expression through the address dictionary. On the
call-free entry-loop body and on every empty-body return the two agree
unconditionally; they agree on a nested direct call exactly when the observable
resolution returns the same name the typed scheduler reads. This is the exact
premise recorded by `Resolves`.

The prepared tensor derivative entry runs in the void loop-call machine
(`CLoops.Calls.machine`, the level of `Rumoca.CTensor.Lowering.CallCorrect`),
whose nested calls are the emitted tensor helper functions, all direct calls by
identifier. Under `Resolves` for the call sites the run visits, the same
execution embeds step for step into the observable machine
(`CCalls.Events.internalNext`), reaching the identical final heap. This mirrors
`CCalls.Typed.loop_call_result`, which performs the same embedding into the
typed machine; only the call-site lemma changes. -/
noncomputable section
namespace Rumoca.CCalls.Events
open CTree CMemory CLoops
variable {E : Type}
variable [interface : CInterface]

/-- The observable call resolution agrees with the direct name a void loop call
reads, at one loop-call state. Trivially true unless the state is poised on a
direct `eval` call. -/
def Resolves (program : Program E) : CLoops.Calls.State → Prop
  | .body (.running (.eval (.call (.id name) _args) :: _) env _ heap) _ =>
      (env name).isSome = false → resolve program env heap (.id name) = some name
  | _ => True

/-- A single direct void loop-call entry lifts into the observable scheduler
when the observable resolution returns the same callee name. -/
theorem enter_loop_call_events (program : Program E) (s : CLoops.State)
    (stack : CLoops.Calls.Continuation) (t : CLoops.Calls.State)
    (h : CLoops.Calls.enterCall s stack = some t)
    (resolves : Resolves program (.body s stack)) :
    enterCall program s "void" (Typed.loopContinuation stack) = some (Typed.loopState t) := by
  unfold CLoops.Calls.enterCall at h
  split at h
  · rename_i name args rest env types heap
    by_cases shadowed : (env name).isSome || name = "isfinite"
    · simp only [if_pos shadowed] at h
      cases h
    · rw [if_neg shadowed] at h
      have unshadowed : (env name).isSome = false := by
        simp only [Bool.or_eq_true, not_or] at shadowed
        simpa using shadowed.1
      have hres : resolve program env heap (.id name) = some name := resolves unshadowed
      cases ha : CCalls.arguments env heap args with
      | none => simp [ha] at h
      | some values =>
        simp only [ha, bind, Option.bind_some, pure] at h
        cases h
        simp only [enterCall, Indirect.operand, bind, Option.bind_some, hres, ha,
          Typed.loopState, Typed.loopContinuation, pure]
  · cases h

/-- One void loop-call step embeds into the observable scheduler. Mirrors
`CCalls.Typed.loop_step`; only the call-site case differs. -/
theorem loop_step_events (program : Program E) (definitions : CLoops.Calls.Definitions)
    (linked : Typed.Extends definitions program.internal) (s t : CLoops.Calls.State)
    (h : CLoops.Calls.next definitions s = some t) (resolves : Resolves program s) :
    internalNext program (Typed.loopState s) = some (Typed.loopState t) := by
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
        simp only [Typed.loopState, internalNext, Typed.nextWith, CCalls.returnCast,
          ↓reduceIte, void, bind, Option.bind_some, pure]
      · rw [if_neg void] at h
        cases h
    | running code locals types heap =>
      cases hn : CLoops.next (.running code locals types heap) with
      | none =>
        simp only [CLoops.Calls.next, hn] at h
        simpa only [Typed.loopState, internalNext, Typed.nextWith, hn]
          using enter_loop_call_events program _ stack t h resolves
      | some following =>
        simp only [CLoops.Calls.next, hn, Option.some.injEq] at h
        subst t
        simp only [Typed.loopState, internalNext, Typed.nextWith, hn]
  | calling name args heap stack =>
    cases hd : definitions name with
    | none => simp [CLoops.Calls.next, hd] at h
    | some fn =>
      have hp := linked name fn hd
      simp only [CLoops.Calls.next, hd, bind, Option.bind_some] at h
      by_cases void : fn.signature.result = "void"
      · rw [if_neg (not_not_intro void)] at h
        cases ha : CCalls.parameters fn.signature.parameters args with
        | none => simp [ha] at h
        | some locals =>
          cases ht : CLoops.Calls.parameterTypes fn.signature.parameters with
          | none => simp [ha, ht] at h
          | some tys =>
            simp only [ha, ht, Option.bind_some, pure] at h
            cases h
            simp only [Typed.loopState, internalNext, Typed.nextWith, hp, ha, ht, void,
              bind, Option.bind_some, pure]
      · rw [if_pos void] at h
        cases h

/-- A completed void loop-call run embeds into the observable scheduler when the
call sites it visits resolve directly. -/
theorem loop_reaches_events (program : Program E) (definitions : CLoops.Calls.Definitions)
    (linked : Typed.Extends definitions program.internal) {s t : CLoops.Calls.State}
    (h : Transition.Reaches (CLoops.Calls.machine definitions).step s t)
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step s v → Resolves program v) :
    Transition.Reaches (fun a b => internalNext program a = some b) (Typed.loopState s) (Typed.loopState t) := by
  induction h with
  | refl => exact .refl _
  | @next s u w hs _ ih =>
    refine .next (loop_step_events program definitions linked s u hs (resolves s (.refl _))) ?_
    exact ih (fun v reach => resolves v (.next hs reach))

/-- A terminating void loop-call behavior embeds into the observable scheduler. -/
theorem loop_terminates_reaches_events (program : Program E) (definitions : CLoops.Calls.Definitions)
    (linked : Typed.Extends definitions program.internal) {s : CLoops.Calls.State} {finalHeap : Heap}
    (h : (CLoops.Calls.machine definitions).Behaves s (.terminates finalHeap))
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step s v → Resolves program v) :
    Transition.Reaches (fun a b => internalNext program a = some b)
      (Typed.loopState s) (.halted ⟨.void, finalHeap⟩) := by
  cases h with
  | terminates ran final =>
    rename_i last
    cases last <;> simp [CLoops.Calls.machine] at final
    cases final
    exact loop_reaches_events program definitions linked ran resolves

/-! ### Appending an outer caller in the observable scheduler

The observable scheduler shares the typed `resume`, so `CCalls.Typed.resume_append`
transfers unchanged; only the call-site `enter_append` needs an observable
variant. -/

theorem enter_append_events (program : Program E) (s : CLoops.State) (resultType : String)
    (stack outer : Typed.Continuation) :
    enterCall program s resultType (stack.append outer) =
      (enterCall program s resultType stack).map (fun t => t.append outer) := by
  cases s with
  | returned => rfl
  | running code env types heap =>
    cases code with
    | nil => by_cases h : resultType = "void" <;> simp [enterCall, h, Typed.State.append]
    | cons stmt rest =>
      cases ho : Indirect.operand stmt with
      | none => simp [enterCall, ho]
      | some operand =>
        cases hr : resolve program env heap operand.callee with
        | none => simp [enterCall, ho, hr]
        | some name =>
          cases ha : arguments env heap operand.args with
          | none => simp [enterCall, ho, hr, ha]
          | some values =>
            simp only [enterCall, ho, hr, ha, bind, Option.bind_some, pure,
              Option.map_some, Typed.State.append, Typed.Continuation.append]

theorem append_step_events (program : Program E) (s t : Typed.State) (outer : Typed.Continuation)
    (h : internalNext program s = some t) :
    Transition.Reaches (fun a b => internalNext program a = some b) (s.append outer) (t.append outer) := by
  cases s with
  | halted => simp [internalNext, Typed.nextWith] at h
  | returning value heap stack =>
    cases stack with
    | done =>
      simp only [internalNext, Typed.nextWith, Typed.resume, Option.some.injEq] at h
      cases h
      exact .refl _
    | caller destination rest env types resultType stack =>
      refine Transition.Reaches.next (t := t.append outer) ?_ (.refl _)
      have := CCalls.Typed.resume_append value heap destination rest env types resultType stack outer
      change internalNext program (.returning value heap ((Typed.Continuation.caller destination rest env types resultType stack).append outer)) = _
      simp only [internalNext, Typed.nextWith, Typed.Continuation.append]
      rw [this]
      change internalNext program (.returning value heap (Typed.Continuation.caller destination rest env types resultType stack)) = some t at h
      simp only [internalNext, Typed.nextWith] at h
      exact congrArg (Option.map (fun t => t.append outer)) h
  | calling name args heap stack =>
    refine Transition.Reaches.next (t := t.append outer) ?_ (.refl _)
    cases hd : program.internal.definitions name with
    | none => simp [internalNext, Typed.nextWith, hd] at h
    | some d => cases d with
      | kernel fn =>
        cases he : CCalls.kernelEntry fn args <;> simp [internalNext, Typed.nextWith, hd, he] at h
        cases h
        simp [internalNext, Typed.nextWith, Typed.State.append, hd, he]
      | tree fn =>
        cases ha : CCalls.parameters fn.signature.parameters args with
        | none => simp [internalNext, Typed.nextWith, hd, ha] at h
        | some env =>
          cases ht : CLoops.Calls.parameterTypes fn.signature.parameters <;>
            simp [internalNext, Typed.nextWith, hd, ha, ht] at h
          cases h
          simp [internalNext, Typed.nextWith, Typed.State.append, hd, ha, ht]
  | kernel state heap stack =>
    refine Transition.Reaches.next (t := t.append outer) ?_ (.refl _)
    cases state with
    | returned x =>
      simp only [internalNext, Typed.nextWith, Option.some.injEq] at h
      cases h
      rfl
    | entry fn x n =>
      cases he : CStatements.next program.internal.kernel (.entry fn x n) <;>
        simp [internalNext, Typed.nextWith, he] at h
      cases h
      simp [internalNext, Typed.nextWith, Typed.State.append, he]
    | running code locals =>
      cases he : CStatements.next program.internal.kernel (.running code locals) <;>
        simp [internalNext, Typed.nextWith, he] at h
      cases h
      simp [internalNext, Typed.nextWith, Typed.State.append, he]
  | body state resultType stack =>
    refine Transition.Reaches.next (t := t.append outer) ?_ (.refl _)
    cases state with
    | returned result =>
      cases hc : CCalls.returnCast resultType result.value <;>
        simp [internalNext, Typed.nextWith, hc] at h
      cases h
      simp [internalNext, Typed.nextWith, Typed.State.append, hc]
    | running code env types heap =>
      cases hn : CLoops.next (.running code env types heap) with
      | none =>
        simp only [internalNext, Typed.nextWith, hn] at h
        simp only [internalNext, Typed.nextWith, Typed.State.append, hn,
          enter_append_events, h, Option.map_some]
      | some following =>
        simp only [internalNext, Typed.nextWith, hn, Option.some.injEq] at h
        subst t
        simp only [internalNext, Typed.nextWith, Typed.State.append, hn]

theorem append_reaches_events (program : Program E) {s t : Typed.State}
    (h : Transition.Reaches (fun a b => internalNext program a = some b) s t) (outer : Typed.Continuation) :
    Transition.Reaches (fun a b => internalNext program a = some b) (s.append outer) (t.append outer) := by
  induction h with
  | refl => exact .refl _
  | next hs _ ih => exact (append_step_events program _ _ outer hs).trans ih

/-- The transfer lemma: a terminating void loop-call of `name` embeds into the
observable machine under any saved caller, reaching the identical final heap,
provided the direct call sites it visits resolve to their own names. -/
theorem loop_call_reaches_events (program : Program E) (definitions : CLoops.Calls.Definitions)
    (linked : Typed.Extends definitions program.internal) {name : String} {args : List Value}
    {heap finalHeap : Heap}
    (h : (CLoops.Calls.machine definitions).Behaves (.calling name args heap .done) (.terminates finalHeap))
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling name args heap .done) v → Resolves program v) (outer : Typed.Continuation) :
    Transition.Reaches (fun a b => internalNext program a = some b)
      (.calling name args heap outer) (.returning .void finalHeap outer) :=
  append_reaches_events program (loop_terminates_reaches_events program definitions linked h resolves) outer

/-- The transfer lemma in behavior form: on its own the observable call has the
identical sole terminating behavior, returning `void` with the same final heap. -/
theorem loop_call_behaviors_events (program : Program E) (definitions : CLoops.Calls.Definitions)
    (linked : Typed.Extends definitions program.internal) {name : String} {args : List Value}
    {heap finalHeap : Heap}
    (h : (CLoops.Calls.machine definitions).Behaves (.calling name args heap .done) (.terminates finalHeap))
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling name args heap .done) v → Resolves program v) (behavior) :
    (machine program).Behaves (.calling name args heap .done) behavior ↔
      behavior = .terminates [] ⟨.void, finalHeap⟩ :=
  (internal_prefix program (loop_call_reaches_events program definitions linked h resolves .done)
    (return_forced program _ _)).behaviors behavior

end Rumoca.CCalls.Events
