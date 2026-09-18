import RumocaCore.Constant.Semantics
import RumocaCore.Tensor

/-! Prepared FMI 3 deployment data for one constant-rate (G01) problem. This is
the constant-rate analog of `TensorFMI3Model`: a model name paired with the
owned constant-rate initial value problem over `N` states. It carries no source
names, resolution or differentiation decisions.

The constant-rate profile exposes no input tensor and no dense output; its state
is a homogeneous vector of `N` scalar states. The state region is one contiguous
`double` array of extent `N`, addressed as the rank-1 shape `⟨[N]⟩` whose volume
is `N`, so the record layout, the model description and the numerical kernel all
keep the state count symbolic and enumerate no coordinate. -/
namespace Rumoca.Solve
open Rumoca.Tensor Rumoca.ConstantProfile

structure ConstantFMI3Model (n : Nat) where
  name : String
  ivp : ConstantIVP n

/-- The state shape of the constant-rate model: a rank-1 vector of the state
count `N`, whose volume is `N`. The FMI-visible state, derivative and time
regions of the record are addressed at this shape. -/
def ConstantFMI3Model.shape (_ : ConstantFMI3Model n) : Shape := ⟨[n]⟩

/-- The state shape's volume is the state count. -/
theorem ConstantFMI3Model.shape_volume (m : ConstantFMI3Model n) : m.shape.volume = n := by
  simp [ConstantFMI3Model.shape, Shape.volume]

/-- The constant-rate profile never exposes a dense (Jacobian) output. -/
def ConstantFMI3Model.hasOutput (_ : ConstantFMI3Model n) : Bool := false

end Rumoca.Solve
