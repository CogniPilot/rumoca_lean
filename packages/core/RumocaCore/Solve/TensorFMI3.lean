import RumocaCore.Solve.Pointwise
import RumocaCore.Solve.Interface

/-! Prepared FMI 3 deployment data for one pointwise tensor problem. This is the
tensor analog of the scalar `FMI3Model`: a model name, the owned executable
kernel and the resolved declared interface of the source. Tensor rank and
extents stay symbolic in the shape parameter and native in every declaration.
The optional prepared diagonal observation records whether the problem exposes
an explicit dense (Jacobian) output. -/
namespace Rumoca.Solve
open Rumoca.Tensor

structure TensorFMI3Model (shape : Shape) where
  name : String
  ivp : PointwiseIVP shape
  interface : Interface
  deriving Repr

/-- Whether the prepared problem carries an explicit dense (Jacobian) output. -/
def TensorFMI3Model.hasOutput (m : TensorFMI3Model shape) : Bool := m.ivp.diagonal.isSome

end Rumoca.Solve
