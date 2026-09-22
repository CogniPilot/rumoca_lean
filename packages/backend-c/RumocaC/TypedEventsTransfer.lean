import RumocaC.TypedCallProofs
import RumocaC.CallEvents

/-! Expression-parametric transfer of finite void loop-call executions into
the observable call machine.

The source is `CLoops.Calls.machineWith expressions`; the target uses
`CCalls.Typed.nextWithExpressions expressions` with observable call entry.
Both use the SAME expression pair for loop execution and argument evaluation.
`ResolvesWith expressions program` requires observable direct-call resolution
to agree at every reachable source state, including nested callees and saved
continuations. Definition-table extension and the source execution stay explicit.

A completed run reaches the identical final heap. Appending an arbitrary outer
caller reaches its return endpoint without executing that caller. Only the
standalone call is characterized by its sole terminating observable behavior.
There is no transfer between different expression pairs and no assertion about
arbitrary stuck or divergent source runs. Field-free old-to-context transfer is
a separate obligation, not supplied by these lemmas.

The original theorem headers and `Resolves` remain empty-context wrappers. -/
noncomputable section
namespace Rumoca.CCalls.Events
open CTree CMemory CLoops
variable {E : Type}
variable [interface : CInterface]

/-- The observable call resolution agrees with the direct name a void loop call
reads, at one loop-call state. Trivially true unless the state is poised on a
direct `eval` call. -/
def ResolvesWith (expressions : CBody.Expressions) (program : Program E) : CLoops.Calls.State → Prop
  | .body (.running (.eval (.call (.id name) _args) :: _) env _ heap) _ =>
      (env name).isSome = false → resolveWith expressions program env heap (.id name) = some name
  | _ => True

/-- A single direct void loop-call entry lifts into the observable scheduler
when the observable resolution returns the same callee name. -/
theorem enter_loop_call_events_with (expressions : CBody.Expressions) (program : Program E) (s : CLoops.State)
    (stack : CLoops.Calls.Continuation) (t : CLoops.Calls.State)
    (h : CLoops.Calls.enterCallWith expressions s stack = some t)
    (resolves : ResolvesWith expressions program (.body s stack)) :
    enterCallWith expressions program s "void" (Typed.loopContinuation stack) = some (Typed.loopState t) := by
  unfold CLoops.Calls.enterCallWith at h
  split at h
  · rename_i name args rest env types heap
    by_cases shadowed : (env name).isSome || name = "isfinite"
    · simp only [if_pos shadowed] at h
      cases h
    · rw [if_neg shadowed] at h
      have unshadowed : (env name).isSome = false := by
        simp only [Bool.or_eq_true, not_or] at shadowed
        simpa using shadowed.1
      have hres : resolveWith expressions program env heap (.id name) = some name := resolves unshadowed
      cases ha : CCalls.argumentsWith expressions env heap args with
      | none => simp [ha] at h
      | some values =>
        simp only [ha, bind, Option.bind_some, pure] at h
        cases h
        simp only [enterCallWith, Indirect.operand, bind, Option.bind_some, hres, ha,
          Typed.loopState, Typed.loopContinuation, pure]
  · cases h

/-- One void loop-call step embeds into the observable scheduler. Mirrors
`CCalls.Typed.loop_step`; only the call-site case differs. -/
theorem loop_step_events_with (expressions : CBody.Expressions) (program : Program E) (definitions : CLoops.Calls.Definitions)
    (linked : Typed.Extends definitions program.internal) (s t : CLoops.Calls.State)
    (h : CLoops.Calls.nextWith expressions definitions s = some t) (resolves : ResolvesWith expressions program s) :
    internalNextWith expressions program (Typed.loopState s) = some (Typed.loopState t) := by
  cases s with
  | halted => cases h
  | returning heap stack =>
    cases stack <;> simp only [CLoops.Calls.nextWith, Option.some.injEq] at h <;> subst t <;> rfl
  | body state stack =>
    cases state with
    | returned result =>
      simp only [CLoops.Calls.nextWith] at h
      by_cases void : result.value = .void
      · rw [if_pos void] at h
        cases h
        simp only [Typed.loopState, internalNextWith, Typed.nextWithExpressions, CCalls.returnCast,
          ↓reduceIte, void, bind, Option.bind_some, pure]
      · rw [if_neg void] at h
        cases h
    | running code locals types heap =>
      cases hn : CLoops.nextWith expressions (.running code locals types heap) with
      | none =>
        simp only [CLoops.Calls.nextWith, hn] at h
        simpa only [Typed.loopState, internalNextWith, Typed.nextWithExpressions, hn]
          using enter_loop_call_events_with expressions program _ stack t h resolves
      | some following =>
        simp only [CLoops.Calls.nextWith, hn, Option.some.injEq] at h
        subst t
        simp only [Typed.loopState, internalNextWith, Typed.nextWithExpressions, hn]
  | calling name args heap stack =>
    cases hd : definitions name with
    | none => simp [CLoops.Calls.nextWith, hd] at h
    | some fn =>
      have hp := linked name fn hd
      simp only [CLoops.Calls.nextWith, hd, bind, Option.bind_some] at h
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
            simp only [Typed.loopState, internalNextWith, Typed.nextWithExpressions, hp, ha, ht, void,
              bind, Option.bind_some, pure]
      · rw [if_pos void] at h
        cases h

/-- A completed void loop-call run embeds into the observable scheduler when the
call sites it visits resolveWith directly. -/
theorem loop_reaches_events_with (expressions : CBody.Expressions) (program : Program E) (definitions : CLoops.Calls.Definitions)
    (linked : Typed.Extends definitions program.internal) {s t : CLoops.Calls.State}
    (h : Transition.Reaches (CLoops.Calls.machineWith expressions definitions).step s t)
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machineWith expressions definitions).step s v → ResolvesWith expressions program v) :
    Transition.Reaches (fun a b => internalNextWith expressions program a = some b) (Typed.loopState s) (Typed.loopState t) := by
  induction h with
  | refl => exact .refl _
  | @next s u w hs _ ih =>
    refine .next (loop_step_events_with expressions program definitions linked s u hs (resolves s (.refl _))) ?_
    exact ih (fun v reach => resolves v (.next hs reach))

/-- A terminating void loop-call behavior embeds into the observable scheduler. -/
theorem loop_terminates_reaches_events_with (expressions : CBody.Expressions) (program : Program E) (definitions : CLoops.Calls.Definitions)
    (linked : Typed.Extends definitions program.internal) {s : CLoops.Calls.State} {finalHeap : Heap}
    (h : (CLoops.Calls.machineWith expressions definitions).Behaves s (.terminates finalHeap))
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machineWith expressions definitions).step s v → ResolvesWith expressions program v) :
    Transition.Reaches (fun a b => internalNextWith expressions program a = some b)
      (Typed.loopState s) (.halted ⟨.void, finalHeap⟩) := by
  cases h with
  | terminates ran final =>
    rename_i last
    cases last <;> simp [CLoops.Calls.machineWith] at final
    cases final
    exact loop_reaches_events_with expressions program definitions linked ran resolves

/-! ### Appending an outer caller in the observable scheduler

The observable scheduler uses canonical `Typed.resumeWith expressions`.
The next lemma generalizes its append property without changing the scheduler
or the legacy theorem in TypedCallProofs. -/

theorem resume_append_events_with (expressions : CBody.Expressions) (value : Value) (heap : Heap) (destination : Destination) (rest : List Stmt)
    (env : CBody.Locals) (types : Types) (resultType : String) (stack outer : Typed.Continuation) :
    Typed.resumeWith expressions value heap (.caller destination rest env types resultType (stack.append outer)) =
      (Typed.resumeWith expressions value heap (.caller destination rest env types resultType stack)).map (fun t => t.append outer) := by
  cases destination with
  | discard => rfl
  | ret => cases h : returnCast resultType value <;> simp [Typed.resumeWith, h, Typed.State.append]
  | declare type name =>
    by_cases hf : (env name).isSome
    · simp [Typed.resumeWith, hf]
    · cases ht : interface.types type with
      | none => simp [Typed.resumeWith, hf, ht]
      | some declared => cases hc : convert declared value <;> simp [Typed.resumeWith, hf, ht, hc, Typed.State.append]
  | assign target =>
    cases target <;>
      simp only [Typed.resumeWith, bind, pure, Option.map_bind, Function.comp_def, Option.map_some, Typed.State.append]


theorem enter_append_events_with (expressions : CBody.Expressions) (program : Program E) (s : CLoops.State) (resultType : String)
    (stack outer : Typed.Continuation) :
    enterCallWith expressions program s resultType (stack.append outer) =
      (enterCallWith expressions program s resultType stack).map (fun t => t.append outer) := by
  cases s with
  | returned => rfl
  | running code env types heap =>
    cases code with
    | nil => by_cases h : resultType = "void" <;> simp [enterCallWith, h, Typed.State.append]
    | cons stmt rest =>
      cases ho : Indirect.operand stmt with
      | none => simp [enterCallWith, ho]
      | some operand =>
        cases hr : resolveWith expressions program env heap operand.callee with
        | none => simp [enterCallWith, ho, hr]
        | some name =>
          cases ha : argumentsWith expressions env heap operand.args with
          | none => simp [enterCallWith, ho, hr, ha]
          | some values =>
            simp only [enterCallWith, ho, hr, ha, bind, Option.bind_some, pure,
              Option.map_some, Typed.State.append, Typed.Continuation.append]

theorem append_step_events_with (expressions : CBody.Expressions) (program : Program E) (s t : Typed.State) (outer : Typed.Continuation)
    (h : internalNextWith expressions program s = some t) :
    Transition.Reaches (fun a b => internalNextWith expressions program a = some b) (s.append outer) (t.append outer) := by
  cases s with
  | halted => simp [internalNextWith, Typed.nextWithExpressions] at h
  | returning value heap stack =>
    cases stack with
    | done =>
      simp only [internalNextWith, Typed.nextWithExpressions, Typed.resumeWith, Option.some.injEq] at h
      cases h
      exact .refl _
    | caller destination rest env types resultType stack =>
      refine Transition.Reaches.next (t := t.append outer) ?_ (.refl _)
      have := resume_append_events_with expressions value heap destination rest env types resultType stack outer
      change internalNextWith expressions program (.returning value heap ((Typed.Continuation.caller destination rest env types resultType stack).append outer)) = _
      simp only [internalNextWith, Typed.nextWithExpressions, Typed.Continuation.append]
      rw [this]
      change internalNextWith expressions program (.returning value heap (Typed.Continuation.caller destination rest env types resultType stack)) = some t at h
      simp only [internalNextWith, Typed.nextWithExpressions] at h
      exact congrArg (Option.map (fun t => t.append outer)) h
  | calling name args heap stack =>
    refine Transition.Reaches.next (t := t.append outer) ?_ (.refl _)
    cases hd : program.internal.definitions name with
    | none => simp [internalNextWith, Typed.nextWithExpressions, hd] at h
    | some d => cases d with
      | kernel fn =>
        cases he : CCalls.kernelEntry fn args <;> simp [internalNextWith, Typed.nextWithExpressions, hd, he] at h
        cases h
        simp [internalNextWith, Typed.nextWithExpressions, Typed.State.append, hd, he]
      | tree fn =>
        cases ha : CCalls.parameters fn.signature.parameters args with
        | none => simp [internalNextWith, Typed.nextWithExpressions, hd, ha] at h
        | some env =>
          cases ht : CLoops.Calls.parameterTypes fn.signature.parameters <;>
            simp [internalNextWith, Typed.nextWithExpressions, hd, ha, ht] at h
          cases h
          simp [internalNextWith, Typed.nextWithExpressions, Typed.State.append, hd, ha, ht]
  | kernel state heap stack =>
    refine Transition.Reaches.next (t := t.append outer) ?_ (.refl _)
    cases state with
    | returned x =>
      simp only [internalNextWith, Typed.nextWithExpressions, Option.some.injEq] at h
      cases h
      rfl
    | entry fn x n =>
      cases he : CStatements.next program.internal.kernel (.entry fn x n) <;>
        simp [internalNextWith, Typed.nextWithExpressions, he] at h
      cases h
      simp [internalNextWith, Typed.nextWithExpressions, Typed.State.append, he]
    | running code locals =>
      cases he : CStatements.next program.internal.kernel (.running code locals) <;>
        simp [internalNextWith, Typed.nextWithExpressions, he] at h
      cases h
      simp [internalNextWith, Typed.nextWithExpressions, Typed.State.append, he]
  | body state resultType stack =>
    refine Transition.Reaches.next (t := t.append outer) ?_ (.refl _)
    cases state with
    | returned result =>
      cases hc : CCalls.returnCast resultType result.value <;>
        simp [internalNextWith, Typed.nextWithExpressions, hc] at h
      cases h
      simp [internalNextWith, Typed.nextWithExpressions, Typed.State.append, hc]
    | running code env types heap =>
      cases hn : CLoops.nextWith expressions (.running code env types heap) with
      | none =>
        simp only [internalNextWith, Typed.nextWithExpressions, hn] at h
        simp only [internalNextWith, Typed.nextWithExpressions, Typed.State.append, hn,
          enter_append_events_with, h, Option.map_some]
      | some following =>
        simp only [internalNextWith, Typed.nextWithExpressions, hn, Option.some.injEq] at h
        subst t
        simp only [internalNextWith, Typed.nextWithExpressions, Typed.State.append, hn]

theorem append_reaches_events_with (expressions : CBody.Expressions) (program : Program E) {s t : Typed.State}
    (h : Transition.Reaches (fun a b => internalNextWith expressions program a = some b) s t) (outer : Typed.Continuation) :
    Transition.Reaches (fun a b => internalNextWith expressions program a = some b) (s.append outer) (t.append outer) := by
  induction h with
  | refl => exact .refl _
  | next hs _ ih => exact (append_step_events_with expressions program _ _ outer hs).trans ih

/-- The transfer lemma: a terminating void loop-call of `name` embeds into the
observable machine under any saved caller, reaching the identical final heap,
provided the direct call sites it visits resolve to their own names. -/
theorem loop_call_reaches_events_with (expressions : CBody.Expressions) (program : Program E) (definitions : CLoops.Calls.Definitions)
    (linked : Typed.Extends definitions program.internal) {name : String} {args : List Value}
    {heap finalHeap : Heap}
    (h : (CLoops.Calls.machineWith expressions definitions).Behaves (.calling name args heap .done) (.terminates finalHeap))
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machineWith expressions definitions).step
      (.calling name args heap .done) v → ResolvesWith expressions program v) (outer : Typed.Continuation) :
    Transition.Reaches (fun a b => internalNextWith expressions program a = some b)
      (.calling name args heap outer) (.returning .void finalHeap outer) :=
  append_reaches_events_with expressions program (loop_terminates_reaches_events_with expressions program definitions linked h resolves) outer

/-- The transfer lemma in behavior form: on its own the observable call has the
identical sole terminating behavior, returning `void` with the same final heap. -/
theorem loop_call_behaviors_events_with (expressions : CBody.Expressions) (program : Program E) (definitions : CLoops.Calls.Definitions)
    (linked : Typed.Extends definitions program.internal) {name : String} {args : List Value}
    {heap finalHeap : Heap}
    (h : (CLoops.Calls.machineWith expressions definitions).Behaves (.calling name args heap .done) (.terminates finalHeap))
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machineWith expressions definitions).step
      (.calling name args heap .done) v → ResolvesWith expressions program v) (behavior) :
    (machineWith expressions program).Behaves (.calling name args heap .done) behavior ↔
      behavior = .terminates [] ⟨.void, finalHeap⟩ :=
  (internal_prefix_with expressions program (loop_call_reaches_events_with expressions program definitions linked h resolves .done)
    (return_forced_with expressions program _ _)).behaviors behavior

/-- Empty-context compatibility facade; all previous theorem headers are retained. -/
abbrev Resolves (program : Program E) := ResolvesWith CBody.legacyExpressions program

theorem enter_loop_call_events (program : Program E) (s : CLoops.State)
    (stack : CLoops.Calls.Continuation) (t : CLoops.Calls.State)
    (h : CLoops.Calls.enterCall s stack = some t)
    (resolves : Resolves program (.body s stack)) :
    enterCall program s "void" (Typed.loopContinuation stack) = some (Typed.loopState t) :=
  enter_loop_call_events_with CBody.legacyExpressions program s stack t h resolves

theorem loop_step_events (program : Program E) (definitions : CLoops.Calls.Definitions)
    (linked : Typed.Extends definitions program.internal) (s t : CLoops.Calls.State)
    (h : CLoops.Calls.next definitions s = some t) (resolves : Resolves program s) :
    internalNext program (Typed.loopState s) = some (Typed.loopState t) :=
  loop_step_events_with CBody.legacyExpressions program definitions linked s t h resolves

theorem loop_reaches_events (program : Program E) (definitions : CLoops.Calls.Definitions)
    (linked : Typed.Extends definitions program.internal) {s t : CLoops.Calls.State}
    (h : Transition.Reaches (CLoops.Calls.machine definitions).step s t)
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step s v → Resolves program v) :
    Transition.Reaches (fun a b => internalNext program a = some b) (Typed.loopState s) (Typed.loopState t) :=
  loop_reaches_events_with CBody.legacyExpressions program definitions linked h resolves

theorem loop_terminates_reaches_events (program : Program E) (definitions : CLoops.Calls.Definitions)
    (linked : Typed.Extends definitions program.internal) {s : CLoops.Calls.State} {finalHeap : Heap}
    (h : (CLoops.Calls.machine definitions).Behaves s (.terminates finalHeap))
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step s v → Resolves program v) :
    Transition.Reaches (fun a b => internalNext program a = some b)
      (Typed.loopState s) (.halted ⟨.void, finalHeap⟩) :=
  loop_terminates_reaches_events_with CBody.legacyExpressions program definitions linked h resolves

theorem enter_append_events (program : Program E) (s : CLoops.State) (resultType : String)
    (stack outer : Typed.Continuation) :
    enterCall program s resultType (stack.append outer) =
      (enterCall program s resultType stack).map (fun t => t.append outer) :=
  enter_append_events_with CBody.legacyExpressions program s resultType stack outer

theorem append_step_events (program : Program E) (s t : Typed.State) (outer : Typed.Continuation)
    (h : internalNext program s = some t) :
    Transition.Reaches (fun a b => internalNext program a = some b) (s.append outer) (t.append outer) :=
  append_step_events_with CBody.legacyExpressions program s t outer h

theorem append_reaches_events (program : Program E) {s t : Typed.State}
    (h : Transition.Reaches (fun a b => internalNext program a = some b) s t) (outer : Typed.Continuation) :
    Transition.Reaches (fun a b => internalNext program a = some b) (s.append outer) (t.append outer) :=
  append_reaches_events_with CBody.legacyExpressions program h outer

theorem loop_call_reaches_events (program : Program E) (definitions : CLoops.Calls.Definitions)
    (linked : Typed.Extends definitions program.internal) {name : String} {args : List Value}
    {heap finalHeap : Heap}
    (h : (CLoops.Calls.machine definitions).Behaves (.calling name args heap .done) (.terminates finalHeap))
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling name args heap .done) v → Resolves program v) (outer : Typed.Continuation) :
    Transition.Reaches (fun a b => internalNext program a = some b)
      (.calling name args heap outer) (.returning .void finalHeap outer) :=
  loop_call_reaches_events_with CBody.legacyExpressions program definitions linked h resolves outer

theorem loop_call_behaviors_events (program : Program E) (definitions : CLoops.Calls.Definitions)
    (linked : Typed.Extends definitions program.internal) {name : String} {args : List Value}
    {heap finalHeap : Heap}
    (h : (CLoops.Calls.machine definitions).Behaves (.calling name args heap .done) (.terminates finalHeap))
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling name args heap .done) v → Resolves program v) (behavior) :
    (machine program).Behaves (.calling name args heap .done) behavior ↔
      behavior = .terminates [] ⟨.void, finalHeap⟩ :=
  loop_call_behaviors_events_with CBody.legacyExpressions program definitions linked h resolves behavior

end Rumoca.CCalls.Events
