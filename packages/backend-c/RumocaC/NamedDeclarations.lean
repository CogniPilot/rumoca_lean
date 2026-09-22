import RumocaC.NamedCallSites

/-! Explicit function calls in fresh local initializers, through the existing
typed call scheduler. The result is converted to the declared local type. -/
noncomputable section
namespace Rumoca.CCalls.Events
open CTree CMemory
variable [interface : CInterface]

theorem named_declare_entry (program : Program E) (env : CBody.Locals) (types : CLoops.Types)
    (heap : Heap) (declaredType destination callee : String) (args : List Expr) (values : List Value)
    (rest : List Stmt) (resultType : String) (stack : Typed.Continuation)
    (fresh : env destination = none) (unshadowed : env callee = none)
    (named : interface.constants callee = none) (ordinary : callee ≠ "isfinite")
    (evaluated : arguments env heap args = some values) :
    internalNext program (.body (.running (.declare declaredType destination (.call (.id callee) args) :: rest)
      env types heap) resultType stack) =
      some (.calling callee values heap (.caller (.declare declaredType destination) rest env types resultType stack)) := by
  simp only [arguments, CBody.legacyExpressions] at evaluated
  simp [internalNext, internalNextWith, Typed.nextWithExpressions, CLoops.nextWith,
    CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith, fresh,
    enterCallWith, Indirect.operand, resolveWith, Indirect.resolveWith, CBody.resolve, CBody.constants,
    unshadowed, named, ordinary, evaluated]

theorem declare_result (program : Program E) (env : CBody.Locals) (types : CLoops.Types)
    (heap : Heap) (declaredType destination : String) (rest : List Stmt) (resultType : String)
    (stack : Typed.Continuation) (value result : Value) (type : CType)
    (fresh : env destination = none) (typed : interface.types declaredType = some type)
    (converted : convert type value = some result) :
    internalNext program (.returning value heap (.caller (.declare declaredType destination) rest env types resultType stack)) =
      some (.body (.running rest (CBody.bind env destination result) (CLoops.bindType types destination type) heap)
        resultType stack) := by
  simp [internalNext, internalNextWith, Typed.nextWithExpressions, Typed.resumeWith, fresh, typed, converted]

end Rumoca.CCalls.Events
