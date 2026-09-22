import RumocaC.ReadOnly
import RumocaC.CallTargets
import RumocaCore.Transition.Events.Simulation

/-! Observable external calls through the shared C scheduler. Uses the same typed
states, argument casts, statement evaluator, kernel and return continuations.
Only function-address lookup and explicit eventful externals are added.
Native function-pointer ABI and call-site prototype compatibility require
separate contracts; addresses here are symbolic program bindings. -/
noncomputable section
namespace Rumoca.CCalls.Events
open CTree CMemory
variable {E : Type}
variable [interface : CInterface]

structure External (E : Type) where
  signature : Signature
  execute : List Value → Heap → List E → Value → Heap → Prop
  result_typed : ∀ args before events result after,
    execute args before events result after →
    returnCast signature.result result = some result
  readonly : ∀ args before events result after,
    execute args before events result after → CReadOnly.Preserves before after

structure Program (E : Type) where
  internal : CCalls.Program
  addresses : Address → Option String
  externals : String → Option (External E)
  disjoint : ∀ name fn, externals name = some fn → internal.definitions name = none
  names : ∀ name fn, externals name = some fn → fn.signature.name = name

def convertedArguments (params : List Parameter) (values : List Value) : Option (List Value) := do
  let env ← parameters params values
  params.mapM fun param => env param.name

def resolveWith (expressions : CBody.Expressions) (p : Program E) (env : CBody.Locals) (heap : Heap) (callee : Expr) : Option String := do
  match ← Indirect.resolveWith expressions env heap callee with
  | .named name => if name = "isfinite" then none else some name
  | .pointer address => p.addresses address

def enterCallWith (expressions : CBody.Expressions) (p : Program E) (s : CLoops.State) (resultType : String)
    (stack : Typed.Continuation) : Option Typed.State :=
  match s with
  | .running [] _ _ heap =>
      if resultType = "void" then some (.returning .void heap stack) else none
  | .running (stmt :: rest) env types heap => do
      let operand ← Indirect.operand stmt
      let name ← resolveWith expressions p env heap operand.callee
      let values ← argumentsWith expressions env heap operand.args
      return .calling name values heap (.caller operand.destination rest env types resultType stack)
  | .returned _ => none

def internalNextWith (expressions : CBody.Expressions) (p : Program E) : Typed.State → Option Typed.State :=
  Typed.nextWithExpressions expressions (enterCallWith expressions p) p.internal

inductive StepWith (expressions : CBody.Expressions) (p : Program E) : Typed.State → List E → Typed.State → Prop where
  | internal : internalNextWith expressions p s = some t → StepWith expressions p s [] t
  | external : p.externals name = some fn →
      convertedArguments fn.signature.parameters args = some values →
      fn.execute values before events result after →
      StepWith expressions p (.calling name args before stack) events (.returning result after stack)

def machineWith (expressions : CBody.Expressions) (p : Program E) : Transition.Events.Machine Typed.State E CBody.Result where
  step := StepWith expressions p
  final | .halted result => some result | _ => none
  final_stuck := by
    intro s result done events t step
    cases s <;> simp only [Option.some.injEq] at done
    all_goals try contradiction

theorem enter_preserves_with (expressions : CBody.Expressions) (p : Program E)
    (step : enterCallWith expressions p s resultType stack = some t) :
    CReadOnly.Preserves (CReadOnly.loopHeap s) (CReadOnly.typedHeap t) := by
  unfold enterCallWith at step
  split at step
  all_goals
    aesop (add safe apply CReadOnly.Preserves.refl)
      (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        CReadOnly.loopHeap, CReadOnly.typedHeap])

theorem internal_preserves_with (expressions : CBody.Expressions) (p : Program E) (step : internalNextWith expressions p s = some t) :
    CReadOnly.Preserves (CReadOnly.typedHeap s) (CReadOnly.typedHeap t) :=
  CReadOnly.typed_nextWithExpressions expressions (enterCallWith expressions p) (fun _ _ _ _ next => enter_preserves_with expressions p next) step

theorem step_preserves_with (expressions : CBody.Expressions) (step : StepWith expressions p s events t) :
    CReadOnly.Preserves (CReadOnly.typedHeap s) (CReadOnly.typedHeap t) := by
  cases step with
  | internal step => exact internal_preserves_with expressions _ step
  | external found converted executed => exact External.readonly _ _ _ _ _ _ executed

theorem reaches_preserves_with (expressions : CBody.Expressions) (run : Transition.Events.Reaches (machineWith expressions p).step s events t) :
    CReadOnly.Preserves (CReadOnly.typedHeap s) (CReadOnly.typedHeap t) := by
  induction run with
  | refl => exact .refl _
  | next first rest ih => exact (step_preserves_with expressions first).trans ih

theorem termination_preserves_with (expressions : CBody.Expressions)
    (behavior : (machineWith expressions p).Behaves s (.terminates events result)) :
    CReadOnly.Preserves (CReadOnly.typedHeap s) result.heap := by
  cases behavior with
  | terminates run done =>
      have preserved := reaches_preserves_with expressions run
      rename_i last
      cases last <;> simp only [machineWith] at done
      all_goals try contradiction
      cases Option.some.inj done
      exact preserved

/-- A foreign binding cannot compete with an internal definition at entry. -/
theorem external_entry_exclusive_with (expressions : CBody.Expressions) (p : Program E) (found : p.externals name = some fn) :
    internalNextWith expressions p (.calling name args heap stack) = none := by
  simp [internalNextWith, Typed.nextWithExpressions, p.disjoint name fn found]

/-- Any supplied external outcome uses the ordinary saved return continuation. -/
theorem external_reaches_with (expressions : CBody.Expressions) (p : Program E) (found : p.externals name = some fn)
    (converted : convertedArguments fn.signature.parameters args = some values)
    (executed : fn.execute values before events result after) (stack : Typed.Continuation) :
    Transition.Events.Reaches (machineWith expressions p).step (.calling name args before stack) events
      (.returning result after stack) := by
  simpa only [List.append_nil] using
    (Transition.Events.Reaches.next (StepWith.external found converted executed)
      (Transition.Events.Reaches.refl (Typed.State.returning result after stack)))

/-- An internal transition cannot compete with a foreign outcome. This uses
only the disjoint definition tables, not global determinism of externals. -/
theorem internal_unique_with (expressions : CBody.Expressions) (p : Program E) (next : internalNextWith expressions p s = some t) :
    ∀ events u, (machineWith expressions p).step s events u → events = [] ∧ u = t := by
  intro events u step
  cases step with
  | internal other => exact ⟨rfl, Option.some.inj (other.symm.trans next)⟩
  | external found converted executed =>
      rw [external_entry_exclusive_with expressions p found] at next
      contradiction

/-- Existing loop transitions are silent transitions of the shared scheduler,
regardless of the program's foreign bindings or later callback behavior. -/
theorem body_step_with (expressions : CBody.Expressions) (p : Program E) (step : CLoops.nextWith expressions s = some t)
    (resultType : String) (stack : Typed.Continuation) :
    internalNextWith expressions p (.body s resultType stack) = some (.body t resultType stack) := by
  cases s with
  | returned => simp [CLoops.nextWith] at step
  | running => simp [internalNextWith, Typed.nextWithExpressions, step]

theorem body_reaches_with (expressions : CBody.Expressions) (p : Program E) (run : Transition.Reaches (CLoops.machineWith expressions).step s t)
    (resultType : String) (stack : Typed.Continuation) :
    Transition.Reaches (fun s t => internalNextWith expressions p s = some t)
      (.body s resultType stack) (.body t resultType stack) := by
  induction run with
  | refl => exact .refl _
  | next first rest ih => exact .next (body_step_with expressions p first resultType stack) ih

/-- Prepend any proved internal prefix to an eventful complete call. -/
theorem internal_prefix_with (expressions : CBody.Expressions) (p : Program E)
    (run : Transition.Reaches (fun s t => internalNextWith expressions p s = some t) s t)
    (rest : Transition.Events.Forced (machineWith expressions p) t events result) :
    Transition.Events.Forced (machineWith expressions p) s events result := by
  induction run with
  | refl => exact rest
  | next first tail ih => exact .next (StepWith.internal first) (internal_unique_with expressions p first) (ih rest)

/-- Ordinary tree entry uses the same parameter and local-type conversion as
all earlier typed-call proofs. -/
theorem tree_entry_with (expressions : CBody.Expressions) (p : Program E) (name : String) (args : List Value) (heap : Heap)
    (stack : Typed.Continuation) (fn : Function) (env : CBody.Locals) (types : CLoops.Types)
    (found : p.internal.definitions name = some (.tree fn))
    (bound : parameters fn.signature.parameters args = some env)
    (typed : CLoops.Calls.parameterTypes fn.signature.parameters = some types) :
    internalNextWith expressions p (.calling name args heap stack) =
      some (.body (.running fn.body env types heap) fn.signature.result stack) := by
  simp [internalNextWith, Typed.nextWithExpressions, found, bound, typed]

/-- A returning foreign outcome with a supplied invocation-local uniqueness
contract can precede any ordinary caller continuation. -/
theorem external_prefix_with (expressions : CBody.Expressions) (p : Program E) (found : p.externals name = some fn)
    (converted : convertedArguments fn.signature.parameters args = some values)
    (executed : fn.execute values before events result after)
    (unique : ∀ trace value heap, fn.execute values before trace value heap →
      trace = events ∧ value = result ∧ heap = after)
    (rest : Transition.Events.Forced (machineWith expressions p) (.returning result after stack) tail final) :
    Transition.Events.Forced (machineWith expressions p) (.calling name args before stack) (events ++ tail) final := by
  refine .next (StepWith.external found converted executed) ?_ rest
  intro trace state step
  cases step with
  | internal next =>
      rw [external_entry_exclusive_with expressions p found] at next
      contradiction
  | external found' converted' executed' =>
      cases Option.some.inj (found'.symm.trans found)
      cases Option.some.inj (converted'.symm.trans converted)
      obtain ⟨rfl, rfl, rfl⟩ := unique _ _ _ executed'
      exact ⟨rfl, rfl⟩

theorem return_forced_with (expressions : CBody.Expressions) (p : Program E) (value : Value) (heap : Heap) :
    Transition.Events.Forced (machineWith expressions p) (.returning value heap .done) [] ⟨value, heap⟩ := by
  refine Transition.Events.Forced.next (m := machineWith expressions p) (first := []) (rest := [])
    (t := Typed.State.halted ⟨value, heap⟩) (StepWith.internal rfl) ?_ (.final rfl)
  intro events state step
  cases step with
  | internal next =>
      have same : Typed.State.halted ⟨value, heap⟩ = state := Option.some.inj next
      exact ⟨rfl, same.symm⟩

/-- An explicit returning, determinate environment contract establishes an
exact external call trace and result. Other externals may be nondeterministic;
no return assumption is silently added to arbitrary host callbacks. -/
theorem external_behaviors_with (expressions : CBody.Expressions) (p : Program E) (found : p.externals name = some fn)
    (converted : convertedArguments fn.signature.parameters args = some values)
    (executed : fn.execute values before events result after)
    (unique : ∀ trace value heap, fn.execute values before trace value heap →
      trace = events ∧ value = result ∧ heap = after) (behavior) :
    (machineWith expressions p).Behaves (.calling name args before .done) behavior ↔
      behavior = .terminates events ⟨result, after⟩ := by
  apply Transition.Events.Forced.behaviors
  simpa only [List.append_nil] using
    external_prefix_with expressions p found converted executed unique (return_forced_with expressions p result after)


/-- Legacy APIs keep the empty-context interpretation. -/
abbrev resolve (p : Program E) := resolveWith CBody.legacyExpressions p
abbrev enterCall (p : Program E) := enterCallWith CBody.legacyExpressions p
abbrev internalNext (p : Program E) := internalNextWith CBody.legacyExpressions p
abbrev Step (p : Program E) := StepWith CBody.legacyExpressions p
abbrev machine (p : Program E) := machineWith CBody.legacyExpressions p

namespace Step
abbrev internal {p : Program E} {s t : Typed.State}
    (step : internalNext p s = some t) : Step p s [] t := StepWith.internal step
abbrev external {p : Program E} {name : String} {fn : External E}
    {args values : List Value} {before after : Heap} {events : List E}
    {result : Value} {stack : Typed.Continuation}
    (found : p.externals name = some fn)
    (converted : convertedArguments fn.signature.parameters args = some values)
    (executed : fn.execute values before events result after) :
    Step p (.calling name args before stack) events (.returning result after stack) :=
  StepWith.external found converted executed
end Step

theorem enter_preserves (p : Program E)
    (step : enterCall p s resultType stack = some t) :
    CReadOnly.Preserves (CReadOnly.loopHeap s) (CReadOnly.typedHeap t) :=
  enter_preserves_with CBody.legacyExpressions p step

theorem internal_preserves (p : Program E) (step : internalNext p s = some t) :
    CReadOnly.Preserves (CReadOnly.typedHeap s) (CReadOnly.typedHeap t) :=
  internal_preserves_with CBody.legacyExpressions p step

theorem step_preserves (step : Step p s events t) :
    CReadOnly.Preserves (CReadOnly.typedHeap s) (CReadOnly.typedHeap t) :=
  step_preserves_with CBody.legacyExpressions step

theorem reaches_preserves (run : Transition.Events.Reaches (machine p).step s events t) :
    CReadOnly.Preserves (CReadOnly.typedHeap s) (CReadOnly.typedHeap t) :=
  reaches_preserves_with CBody.legacyExpressions run

theorem termination_preserves
    (behavior : (machine p).Behaves s (.terminates events result)) :
    CReadOnly.Preserves (CReadOnly.typedHeap s) result.heap :=
  termination_preserves_with CBody.legacyExpressions behavior

theorem external_entry_exclusive (p : Program E) (found : p.externals name = some fn) :
    internalNext p (.calling name args heap stack) = none :=
  external_entry_exclusive_with CBody.legacyExpressions p found

theorem external_reaches (p : Program E) (found : p.externals name = some fn)
    (converted : convertedArguments fn.signature.parameters args = some values)
    (executed : fn.execute values before events result after) (stack : Typed.Continuation) :
    Transition.Events.Reaches (machine p).step (.calling name args before stack) events
      (.returning result after stack) :=
  external_reaches_with CBody.legacyExpressions p found converted executed stack

theorem internal_unique (p : Program E) (next : internalNext p s = some t) :
    ∀ events u, (machine p).step s events u → events = [] ∧ u = t :=
  internal_unique_with CBody.legacyExpressions p next

theorem body_step (p : Program E) (step : CLoops.next s = some t)
    (resultType : String) (stack : Typed.Continuation) :
    internalNext p (.body s resultType stack) = some (.body t resultType stack) :=
  body_step_with CBody.legacyExpressions p step resultType stack

theorem body_reaches (p : Program E) (run : Transition.Reaches CLoops.machine.step s t)
    (resultType : String) (stack : Typed.Continuation) :
    Transition.Reaches (fun s t => internalNext p s = some t)
      (.body s resultType stack) (.body t resultType stack) :=
  body_reaches_with CBody.legacyExpressions p run resultType stack

theorem internal_prefix (p : Program E)
    (run : Transition.Reaches (fun s t => internalNext p s = some t) s t)
    (rest : Transition.Events.Forced (machine p) t events result) :
    Transition.Events.Forced (machine p) s events result :=
  internal_prefix_with CBody.legacyExpressions p run rest

theorem tree_entry (p : Program E) (name : String) (args : List Value) (heap : Heap)
    (stack : Typed.Continuation) (fn : Function) (env : CBody.Locals) (types : CLoops.Types)
    (found : p.internal.definitions name = some (.tree fn))
    (bound : parameters fn.signature.parameters args = some env)
    (typed : CLoops.Calls.parameterTypes fn.signature.parameters = some types) :
    internalNext p (.calling name args heap stack) =
      some (.body (.running fn.body env types heap) fn.signature.result stack) :=
  tree_entry_with CBody.legacyExpressions p name args heap stack fn env types found bound typed

theorem external_prefix (p : Program E) (found : p.externals name = some fn)
    (converted : convertedArguments fn.signature.parameters args = some values)
    (executed : fn.execute values before events result after)
    (unique : ∀ trace value heap, fn.execute values before trace value heap →
      trace = events ∧ value = result ∧ heap = after)
    (rest : Transition.Events.Forced (machine p) (.returning result after stack) tail final) :
    Transition.Events.Forced (machine p) (.calling name args before stack) (events ++ tail) final :=
  external_prefix_with CBody.legacyExpressions p found converted executed unique rest

theorem return_forced (p : Program E) (value : Value) (heap : Heap) :
    Transition.Events.Forced (machine p) (.returning value heap .done) [] ⟨value, heap⟩ :=
  return_forced_with CBody.legacyExpressions p value heap

theorem external_behaviors (p : Program E) (found : p.externals name = some fn)
    (converted : convertedArguments fn.signature.parameters args = some values)
    (executed : fn.execute values before events result after)
    (unique : ∀ trace value heap, fn.execute values before trace value heap →
      trace = events ∧ value = result ∧ heap = after) (behavior) :
    (machine p).Behaves (.calling name args before .done) behavior ↔
      behavior = .terminates events ⟨result, after⟩ :=
  external_behaviors_with CBody.legacyExpressions p found converted executed unique behavior

theorem machine_legacy (p : Program E) :
    machineWith CBody.legacyExpressions p = machine p := rfl

theorem legacy_behaviors (p : Program E) (s : Typed.State) (behavior) :
    (machineWith CBody.legacyExpressions p).Behaves s behavior ↔
      (machine p).Behaves s behavior := Iff.rfl

end Rumoca.CCalls.Events
end
