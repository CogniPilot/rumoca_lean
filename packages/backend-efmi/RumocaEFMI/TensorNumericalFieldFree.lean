import RumocaC.FieldFreeExpressions
import RumocaEFMI.TensorNumericalLinkage

namespace Rumoca.EFMI.TensorNumericalFieldFree
open CTree CMemory CDeclaredMembers.FieldFree
open TensorNumericalLinkage CTensor.ProgramFixture

/-- Kernel reduction of the seven ACTUAL printed trees, not a name-based
execution rule. The predicate descends through every loop and expression. -/
theorem seven_free : numericalFunctions.all (fun fn => body fn.body) = true := by
  rfl

theorem numerical_member (fn : Function) (member : fn ∈ numericalFunctions) :
    AdmittedBody fn.body :=
  List.all_eq_true.mp seven_free fn member

theorem definition_body (name : String) (fn : Function)
    (found : definitions name = some fn) : AdmittedBody fn.body := by
  obtain ⟨member, _⟩ := CCalls.TreeTable.lookup_some numericalFunctions name fn found
  exact numerical_member fn member

/-- The shape-indexed initial/RHS tree certificates do not enumerate coordinates. -/
theorem initial_free (shape : Tensor.Shape) :
    AdmittedBody (IVPEntry.plan shape).initial.function.tree.body :=
  definition_body _ _ (initial_defined shape)

theorem derivative_free (shape : Tensor.Shape) :
    AdmittedBody (IVPEntry.plan shape).derivative.function.tree.body :=
  definition_body _ _ (derivative_defined shape)

theorem square_diagonal_free : AdmittedBody CTensor.SquareDiagonal.function.body :=
  definition_body _ _ square_diagonal_defined

theorem seven_render_and_free :
    TensorProduction.kernelPieces =
      "#include <stddef.h>\n#include <stdint.h>\n" :: numericalFunctions.map Function.render ∧
    ∀ fn ∈ numericalFunctions, AdmittedBody fn.body :=
  ⟨pieces_exact, numerical_member⟩

section
variable [interface : CInterface]

/-- Lookup, syntax and evaluator compatibility share the exact seven-tree table. -/
theorem helper_expression_agreement (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (env : CBody.Locals) (heap : Heap)
    (name : String) (fn : Function) (found : definitions name = some fn)
    (e : Expr) (member : e ∈ fn.body.flatMap expressions) :
    CDeclaredMembers.eval declarations objects env heap e = CBody.eval env heap e ∧
    CDeclaredMembers.lvalue declarations objects env heap e = CBody.lvalue env heap e :=
  body_expression_agreement declarations objects env heap fn.body (definition_body name fn found) e member

end
end Rumoca.EFMI.TensorNumericalFieldFree
