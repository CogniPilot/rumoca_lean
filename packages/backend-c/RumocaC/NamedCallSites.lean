import RumocaC.CallEvents

/-! Actual named-call entry, local-result assignment and expression return.
Arguments and conversions have explicit contracts; no function name stands
for an assumed application-specific result. -/
noncomputable section
namespace Rumoca.CCalls.Events
open CTree CMemory
variable [interface : CInterface]

theorem named_assign_entry (program : Program E) (env : CBody.Locals) (types : CLoops.Types)
    (heap : Heap) (destination callee : String) (args : List Expr) (values : List Value)
    (rest : List Stmt) (resultType : String) (stack : Typed.Continuation)
    (old : Value) (type : CType)
    (present : env destination = some old) (typed : types destination = some type)
    (unshadowed : env callee = none) (named : interface.constants callee = none)
    (ordinary : callee ≠ "isfinite") (evaluated : arguments env heap args = some values) :
    internalNext program (.body (.running (.assign (.id destination) (.call (.id callee) args) :: rest)
      env types heap) resultType stack) =
      some (.calling callee values heap (.caller (.assign (.id destination)) rest env types resultType stack)) := by
  simp only [arguments, CBody.legacyExpressions] at evaluated
  simp [internalNext, internalNextWith, Typed.nextWithExpressions, CLoops.nextWith,
    CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith, present, typed,
    enterCallWith, Indirect.operand, resolveWith, Indirect.resolveWith, CBody.resolve, CBody.constants,
    unshadowed, named, ordinary, evaluated]

theorem assign_result (program : Program E) (env : CBody.Locals) (types : CLoops.Types)
    (heap : Heap) (destination : String) (rest : List Stmt) (resultType : String)
    (stack : Typed.Continuation) (old value result : Value) (type : CType)
    (present : env destination = some old) (typed : types destination = some type)
    (converted : convert type value = some result) :
    internalNext program (.returning value heap (.caller (.assign (.id destination)) rest env types resultType stack)) =
      some (.body (.running rest (CBody.bind env destination result) types heap) resultType stack) := by
  simp [internalNext, internalNextWith, Typed.nextWithExpressions, Typed.resumeWith, present, typed, converted]

theorem expression_return (program : Program E) (env : CBody.Locals) (types : CLoops.Types)
    (heap : Heap) (expr : Expr) (rest : List Stmt) (resultType : String) (stack : Typed.Continuation)
    (value result : Value) (evaluated : CLoops.eval env types heap expr = some value)
    (converted : returnCast resultType value = some result) :
    Transition.Reaches (fun s t => internalNext program s = some t)
      (.body (.running (.ret (some expr) :: rest) env types heap) resultType stack)
      (.returning result heap stack) := by
  have first : CLoops.next (.running (.ret (some expr) :: rest) env types heap) =
      some (.returned ⟨value, heap⟩) := by simp [CLoops.next, CLoops.nextWith, evaluated]
  refine .next (body_step program first resultType stack) ?_
  exact .next (by simp [internalNext, internalNextWith, Typed.nextWithExpressions, converted]) (.refl _)

end Rumoca.CCalls.Events
