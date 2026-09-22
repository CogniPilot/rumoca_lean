import RumocaC.DeclaredMembers
import RumocaC.TypedCalls

/-! Scratch context-aware scheduler cutover. The expression pair is supplied
once to arithmetic, argument evaluation, stores and return destinations. This
is to become shared canonical scheduling with empty-context legacy wrappers,
not a second permanent call-machine implementation. -/
noncomputable section
namespace Rumoca.CContextMachine
open CTree CMemory CLoops CCalls
variable [interface : CInterface]

/-- Compatibility facade over the shared production-owned evaluator/scheduler.
No expression recursion or scheduling implementation lives in this module. -/
abbrev Expressions := CBody.Expressions
abbrev legacy : Expressions := CBody.legacyExpressions
abbrev declared (declarations : CDeclaredMembers.Declarations) (objects : CDeclaredMembers.Objects) :
    Expressions := CBody.declaredExpressions declarations objects
abbrev typedEval := CLoops.evalWith
abbrev loopNext := CLoops.nextWith
abbrev arguments := CCalls.argumentsWith
abbrev enter := Typed.enterCallWith
abbrev resume := Typed.resumeWith
abbrev nextWith := Typed.nextWithExpressions
abbrev next := Typed.nextIn
abbrev machine := Typed.machineWith

theorem typedEval_legacy (env : CBody.Locals) (types : Types) (heap : Heap) (e : Expr) :
    typedEval legacy env types heap e = CLoops.eval env types heap e := rfl

theorem loopNext_legacy (s : CLoops.State) : loopNext legacy s = CLoops.next s := rfl

theorem arguments_legacy (env : CBody.Locals) (heap : Heap) (args : List Expr) :
    arguments legacy env heap args = CCalls.arguments env heap args := rfl

theorem enter_legacy (s : CLoops.State) (type : String) (stack : Typed.Continuation) :
    enter legacy s type stack = Typed.enterCall s type stack := rfl

theorem resume_legacy (value : Value) (heap : Heap) (stack : Typed.Continuation) :
    resume legacy value heap stack = Typed.resume value heap stack := rfl

theorem nextWith_legacy (enterCall) (p : CCalls.Program) (s : Typed.State) :
    nextWith legacy enterCall p s = Typed.nextWith enterCall p s := rfl

theorem next_legacy (p : CCalls.Program) (s : Typed.State) :
    next legacy p s = Typed.next p s := rfl

theorem machine_legacy (p : CCalls.Program) : machine legacy p = Typed.machine p := rfl

/-- Includes termination, stuck execution and divergence; not only one
successful entry/return example. All existing arbitrary programs are covered. -/
theorem legacy_behaviors (p : CCalls.Program) (s : Typed.State) (behavior) :
    (machine legacy p).Behaves s behavior ↔ (Typed.machine p).Behaves s behavior := by
  rw [machine_legacy]

theorem declared_scalar (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects)
    (scalar : ∀ base name, CDeclaredMembers.arrayAt declarations objects base name = none) :
    declared declarations objects = legacy := by
  have values : CDeclaredMembers.eval declarations objects = CBody.eval := by
    funext env heap e
    exact (CDeclaredMembers.scalar_agreement declarations objects scalar env heap e).1
  have addresses : CDeclaredMembers.lvalue declarations objects = CBody.lvalue := by
    funext env heap e
    exact (CDeclaredMembers.scalar_agreement declarations objects scalar env heap e).2
  change CBody.evalWith declarations objects = CBody.eval at values
  change CBody.lvalueWith declarations objects = CBody.lvalue at addresses
  simp only [declared, legacy, CBody.declaredExpressions, CBody.legacyExpressions, values, addresses]

theorem scalar_behaviors (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects)
    (scalar : ∀ base name, CDeclaredMembers.arrayAt declarations objects base name = none)
    (p : CCalls.Program) (s : Typed.State) (behavior) :
    (machine (declared declarations objects) p).Behaves s behavior ↔
      (Typed.machine p).Behaves s behavior := by
  rw [declared_scalar declarations objects scalar]

theorem invoke_step (expressions : Expressions) (p : CCalls.Program) (name : String)
    (args : List Expr) (values : List Value) (rest : List Stmt) (env : CBody.Locals)
    (types : Types) (heap : Heap) (type : String) (stack : Typed.Continuation)
    (ordinary : name ≠ "isfinite") (unshadowed : env name = none)
    (pureCall : expressions.value env heap (.call (.id name) args) = none)
    (evaluated : arguments expressions env heap args = some values) :
    next expressions p (.body (.running (.eval (.call (.id name) args) :: rest) env types heap) type stack) =
      some (.calling name values heap (.caller .discard rest env types type stack)) := by
  simp only [next, Typed.nextIn, Typed.nextWithExpressions, CLoops.nextWith,
    CLoops.evalWith, pureCall, bind, Option.bind_none,
    Typed.enterCallWith, callOperand, Option.bind_some, unshadowed, Option.isSome_none,
    Bool.false_or, decide_eq_true_eq, if_neg ordinary, evaluated, pure]

theorem declared_invoke_step (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program) (name : String)
    (args : List Expr) (values : List Value) (rest : List Stmt) (env : CBody.Locals)
    (types : Types) (heap : Heap) (type : String) (stack : Typed.Continuation)
    (ordinary : name ≠ "isfinite") (unshadowed : env name = none)
    (evaluated : arguments (declared declarations objects) env heap args = some values) :
    next (declared declarations objects) p
      (.body (.running (.eval (.call (.id name) args) :: rest) env types heap) type stack) =
      some (.calling name values heap (.caller .discard rest env types type stack)) := by
  apply invoke_step _ p name args values rest env types heap type stack ordinary unshadowed ?_ evaluated
  simp [declared, CBody.declaredExpressions, CBody.evalWith, ordinary]

end Rumoca.CContextMachine
