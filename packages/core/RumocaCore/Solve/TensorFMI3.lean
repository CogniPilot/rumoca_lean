import RumocaCore.Solve.Pointwise

/-! Prepared FMI 3 deployment data for one pointwise tensor problem. This is the
tensor analog of the scalar `FMI3Model`: a model name paired with the owned
executable kernel. It carries no source names, resolution or differentiation
decisions; tensor rank and extents stay symbolic in the shape parameter. The
optional prepared diagonal observation records whether the problem exposes an
explicit dense (Jacobian) output. -/
namespace Rumoca.Solve
open Rumoca.Tensor

structure TensorFMI3Model (shape : Shape) where
  name : String
  ivp : PointwiseIVP shape
  deriving Repr

/-- Whether the prepared problem carries an explicit dense (Jacobian) output. -/
def TensorFMI3Model.hasOutput (m : TensorFMI3Model shape) : Bool := m.ivp.diagonal.isSome

end Rumoca.Solve
