import RumocaFMI3.Runtime
import RumocaFMI3.TensorInstanceStorage
import RumocaCore.Tensor.Matrix

/-! Calls of the prepared tensor kernel entries over the regions of the instance
record `m`, with the element count given as an expression. Every adapter body that
evaluates the derivative or the dense Jacobian uses these calls: the derivative
getter and `fmi3DoStep` pass the local count `nContinuousStates`, and the Float64
getter passes the record's state volume, so a calculated variable is evaluated
before it is read. -/
namespace Rumoca.FMI3.TensorEntry
open CTree TensorInstance

/-- The arguments of `rumoca_rhs`: the state, input and derivative regions and
the element count. -/
@[simp] def rhsArgs (count : Expr) : List Expr :=
  [Runtime.region stateName, Runtime.region inputName, Runtime.region derivativeName, count]

/-- `rumoca_rhs(&m->x[0], &m->u[0], &m->dx[0], count);` -/
def rhsCall (count : Expr) : Stmt := .eval (Runtime.call "rumoca_rhs" (rhsArgs count))

/-- The arguments of `rumoca_square_jacobian_diag`: the input and output regions,
the element count and the flattened matrix cell count. -/
@[simp] def jacobianArgs (count : Expr) (shape : Tensor.Shape) : List Expr :=
  [Runtime.region inputName, Runtime.region outputName, count,
    Runtime.n (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume]

/-- `rumoca_square_jacobian_diag(&m->u[0], &m->J[0], count, cells);` -/
def jacobianCall (count : Expr) (shape : Tensor.Shape) : Stmt :=
  .eval (Runtime.call "rumoca_square_jacobian_diag" (jacobianArgs count shape))

end Rumoca.FMI3.TensorEntry
