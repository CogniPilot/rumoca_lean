import RumocaCore.Solve.ConstantFMI3
import RumocaCore.Tensor

/-! The C record layout of the constant-rate states. The instance record stores
the `N` scalar source states in declaration order as one contiguous `double`
block, and their derivatives in a second block of the same extent, so the
continuous-state vector and the numerical kernel's whole-vector step address
them directly. This layout belongs to code generation only: the FMI interface
exports each state as its own scalar variable (`ConstantFMI3Model.interface`),
and the Float64 accessors address each one at its element offset. -/
namespace Rumoca.Solve
open Rumoca.Tensor

/-- The contiguous state block of the constant-rate instance record: a rank-1
block whose extent is the state count `N`. -/
def ConstantFMI3Model.shape (_ : ConstantFMI3Model n) : Shape := ⟨[n]⟩

/-- The state block's volume is the state count. -/
theorem ConstantFMI3Model.shape_volume (m : ConstantFMI3Model n) : m.shape.volume = n := by
  simp [ConstantFMI3Model.shape, Shape.volume]

end Rumoca.Solve
