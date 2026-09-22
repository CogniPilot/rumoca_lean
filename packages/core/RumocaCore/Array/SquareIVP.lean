import RumocaCore.Array.Solve

/-! Canonical prepared square IVP index, owned by core. The programs are the
existing Solve programs, including the forward-generated diagonal coefficients.
C storage plans consume this index; this module introduces no new solver,
source matching, shape inference or target representation. -/
namespace Rumoca.ArrayProfile
open Rumoca.Tensor Solve.Tensor

def squareIVP (shape : Shape) : Solve.PointwiseIVP shape :=
  ⟨fill shape .zero, squareProgram shape, some (squareJacobianProgram shape)⟩

/-- Identify an existing successful residual/initial/Jacobian solve with the
canonical index. These are results of the existing solver, not backend choices. -/
theorem Solved.lower_eq_squareIVP (dae : DAE.Model source)
    (initial : DAE.solveInitial? dae.initialResidual = some (fill stateShape .zero))
    (derivative : DAE.solveResidual? dae.residual = some (squareProgram stateShape))
    (diagonal : DAE.solveJacobian? dae.jacobian = some (some (squareJacobianProgram stateShape))) :
    Solved.lower dae = squareIVP stateShape := by
  have checked : Solved.lower? dae = some (squareIVP stateShape) := by
    simp only [Solved.lower?, initial, derivative, diagonal]
    rfl
  exact Option.some.inj ((Solved.lower_checked dae).symm.trans checked)

end Rumoca.ArrayProfile
