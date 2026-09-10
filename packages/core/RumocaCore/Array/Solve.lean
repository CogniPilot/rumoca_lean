import RumocaCore.Array.IR
import RumocaCore.Solve.Pointwise
import RumocaCore.Solve.Tensor.Forward

/-! The tiny DAE solver recognizes the two supported explicit residuals and
fixed-zero initialization. Unknown residuals are rejected. An explicit square
Jacobian is lowered with the proved forward transformation and a prepared
diagonal materializer, keeping both loops and tensor elements out of lowering.
Neither target code nor FMI packaging makes these compilation decisions. -/
namespace Rumoca.ArrayProfile
open Rumoca.Tensor Solve.Tensor

def squareProgram (shape : Shape) : Program [shape, shape] shape :=
  .binary .mul (.there .here) (.there .here) (.ret .here)

/-- Unit input directions and zero state directions are executable constants.
The coefficient program is produced by AD, not by a backend-specific formula. -/
def squareJacobianProgram (shape : Shape) : DiagonalProgram [shape, shape] shape where
  coefficients := .fill shape .zero (.fill shape .one
    ((squareProgram shape).forward (fun r => .there (.there r))
      (Ren.push (.there .here) (Ren.push .here Ren.empty)) .tangent))

theorem square_jacobian_compact (shape : Shape) : (squareJacobianProgram shape).nodeCount = 8 := rfl

theorem diagonal_shape (p : DiagonalProgram [stateShape, stateShape] stateShape) :
    p.shape = jacobianShape := rfl

def DAE.solveResidual? : Expr shape → Option (Program [shape, shape] shape)
  | .sub .derivative .input => some (.ret (.there .here))
  | .sub .derivative (.binary .mul .input .input) => some (squareProgram shape)
  | _ => none

def DAE.solveInitial? : Expr shape → Option (Program [] shape)
  | .sub .state .zero => some (fill shape .zero)
  | _ => none

def DAE.solveJacobian? : Option (Expr shape) → Option (Option (DiagonalProgram [shape, shape] shape))
  | none => some none
  | some (.binary .mul .input .input) => some (some (squareJacobianProgram shape))
  | _ => none

def Solved.lower? (dae : DAE.Model source) : Option (Solve.PointwiseIVP stateShape) := do
  let derivative ← DAE.solveResidual? dae.residual
  let initial ← DAE.solveInitial? dae.initialResidual
  let diagonal ← DAE.solveJacobian? dae.jacobian
  return ⟨initial, derivative, diagonal⟩

theorem Solved.lower_fields (dae : DAE.Model source) (kernel : Solve.PointwiseIVP stateShape)
    (checked : lower? dae = some kernel) :
    ∃ rhs initial diagonal,
      DAE.solveResidual? dae.residual = some rhs ∧
      DAE.solveInitial? dae.initialResidual = some initial ∧
      DAE.solveJacobian? dae.jacobian = some diagonal ∧ kernel = ⟨initial, rhs, diagonal⟩ := by
  cases hr : DAE.solveResidual? dae.residual with
  | none => simp [lower?, hr] at checked
  | some rhs =>
    cases hi : DAE.solveInitial? dae.initialResidual with
    | none => simp [lower?, hr, hi] at checked
    | some initial =>
      cases hj : DAE.solveJacobian? dae.jacobian with
      | none => simp [lower?, hr, hi, hj] at checked
      | some diagonal =>
        simp [lower?, hr, hi, hj] at checked
        exact ⟨rhs, initial, diagonal, rfl, rfl, rfl, checked.symm⟩

/-- Every source-indexed DAE in the admitted development profile is solvable.
This does not make the solver accept other residuals or source grammar cases. -/
theorem Solved.lower_complete (dae : DAE.Model source) : ∃ kernel, lower? dae = some kernel := by
  simp only [lower?, dae.residual_source, dae.initial_source, dae.jacobian_source,
    dae.flat.rhs_source, dae.flat.initial_source, dae.flat.jacobian_source]
  cases source.body <;>
    simp [Flat.rhsFor, Flat.jacobianFor, DAE.lowerExpr, DAE.solveResidual?,
      DAE.solveInitial?, DAE.solveJacobian?]

/-- The rejection arm is unreachable for a source-indexed DAE, by the checked
completeness theorem. The candidate computation remains the partial solver. -/
def Solved.lower (dae : DAE.Model source) : Solve.PointwiseIVP stateShape :=
  match h : lower? dae with
  | some kernel => kernel
  | none => False.elim (by obtain ⟨kernel, hk⟩ := lower_complete dae; rw [h] at hk; cases hk)

theorem Solved.lower_checked (dae : DAE.Model source) : lower? dae = some (lower dae) := by
  unfold lower
  split
  · assumption
  · rename_i h
    obtain ⟨kernel, hk⟩ := lower_complete dae
    rw [h] at hk
    cases hk

end Rumoca.ArrayProfile
