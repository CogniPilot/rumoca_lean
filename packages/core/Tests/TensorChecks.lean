import Tests.TensorChecks.Array_ADExact
import ProofAudit.Audit
import RumocaCore.Tensor.Matrix
import RumocaCore.Tensor.Differentiation
import RumocaCore.Array.Builtin
import RumocaCore.Array.Lowering
import RumocaCore.Array.SquareIVP
import RumocaCore.Array.Finite
import RumocaCore.Solve.Tensor.ReverseProofs
import RumocaCore.Driven.Lowering

namespace Rumoca.TensorChecks
open Rumoca.Tensor

/-- Equal storage volume cannot erase rank or permit a tensor-register mixup. -/
theorem equal_volume_different_shapes :
    (matrixShape 2 3).volume = (Shape.mk [6]).volume ∧ matrixShape 2 3 ≠ ⟨[6]⟩ := by
  decide +kernel

example : True := by
  fail_if_success
    have bad : Value Nat (matrixShape 2 3) := Value.fill ⟨[6]⟩ 0
  trivial

example : True := by
  fail_if_success
    have bad : Solve.Tensor.Ref [matrixShape 2 3] ⟨[6]⟩ := .here
  trivial

/-- The storage bridge agrees with mathlib's row/column ordering, including
an off-diagonal entry that detects accidental transposition. -/
theorem matrix_storage_order :
    (Value.ofMatrix (Matrix.of fun (i : Fin 2) (j : Fin 3) => 10 * i.val + j.val)).data.toArray =
      #[0, 1, 2, 10, 11, 12] := by decide +kernel

theorem empty_matrix_roundtrip (m : Matrix (Fin 0) (Fin 3) Nat) :
    (Value.ofMatrix m).toMatrix = m := Value.toMatrix_ofMatrix m

/-- Initialization cannot be silently changed when the differential equation
would otherwise remain correct. -/
theorem wrong_initialization_rejected (m : Driven.DAE.Model source)
    (input derivative : Value ℝ scalar) :
    ¬ m.Initial (Driven.singleton 1) input derivative := by
  rw [Driven.Solved.lower_initial]
  change ¬ Driven.singleton (1 : ℝ) = Driven.singleton 0
  intro h
  have h := Driven.singleton_injective h
  norm_num at h

#audit axioms equal_volume_different_shapes
#audit axioms matrix_storage_order
#audit axioms empty_matrix_roundtrip
#audit axioms wrong_initialization_rejected
#audit axioms Rumoca.Tensor.Value.getElem_zipWith
#audit axioms Rumoca.Tensor.BinaryOp.eval_correct
#audit axioms Rumoca.Tensor.AD.hasFDerivAt
#audit axioms Rumoca.Tensor.AD.jvp_correct
#audit axioms Rumoca.Tensor.AD.vjp_correct
#audit axioms Rumoca.Tensor.AD.square_hasFDerivAt
#audit axioms Rumoca.Tensor.AD.square_vjp_correct
#audit axioms Rumoca.Tensor.AD.square_jacobian_correct
#audit axioms Rumoca.ArrayProfile.Call.denotes_unique
#audit axioms Rumoca.ArrayProfile.Call.square_correct
#audit axioms Rumoca.ArrayProfile.Model.jacobian_call_correct
#audit axioms Rumoca.Solve.Tensor.Program.evalForward_primal
#audit axioms Rumoca.Solve.Tensor.Program.forward_correct
#audit axioms Rumoca.Solve.Tensor.Program.forward_primal
#audit axioms Rumoca.Solve.Tensor.Program.forward_compact
#audit axioms Rumoca.Solve.Tensor.Program.hasFDerivAt
#audit axioms Rumoca.Solve.Tensor.Program.evalForward_tangent
#audit axioms Rumoca.Solve.Tensor.Program.forward_derivative
#audit axioms Rumoca.Solve.Tensor.Program.reverse_primal
#audit axioms Rumoca.Solve.Tensor.Env.pair_addAt
#audit axioms Rumoca.Solve.Tensor.Program.reverse_pairing
#audit axioms Rumoca.Solve.Tensor.Program.reverse_differential
#audit axioms Rumoca.Solve.Tensor.Program.reverse_derivative
#audit axioms Rumoca.Solve.Tensor.DiagonalProgram.eval_correct
#audit axioms Rumoca.Solve.PointwiseIVP.output_correct
#audit axioms Rumoca.ArrayProfile.Flat.lower_correct
#audit axioms Rumoca.ArrayProfile.Flat.lower_initial
#audit axioms Rumoca.ArrayProfile.DAE.lowerExpr_correct
#audit axioms Rumoca.ArrayProfile.DAE.lower_correct
#audit axioms Rumoca.ArrayProfile.DAE.lower_initial
#audit axioms Rumoca.ArrayProfile.DAE.solveResidual_correct
#audit axioms Rumoca.ArrayProfile.DAE.solveInitial_correct
#audit axioms Rumoca.ArrayProfile.DAE.solveJacobian_correct
#audit axioms Rumoca.ArrayProfile.Solved.lower_complete
#audit axioms Rumoca.ArrayProfile.Solved.lower_checked
#audit axioms Rumoca.ArrayProfile.Solved.lower_eq_squareIVP
#audit axioms Rumoca.ArrayProfile.Solved.lower_correct
#audit axioms Rumoca.ArrayProfile.Solved.lower_initial
#audit axioms Rumoca.ArrayProfile.square_jacobian_eval
#audit axioms Rumoca.ArrayProfile.square_jacobian_compact
#audit axioms Rumoca.ArrayProfile.diagonal_shape
#audit axioms Rumoca.ArrayProfile.lowering_chain_correct
#audit axioms Rumoca.ArrayProfile.initialization_chain_correct
#audit axioms Rumoca.ArrayProfile.square_finite_correct
#audit axioms Rumoca.ArrayProfile.square_finite_nearest
#audit axioms Rumoca.ArrayProfile.square_jacobian_coefficients_finite
#audit axioms Rumoca.ArrayProfile.square_jacobian_coefficients_nearest

end Rumoca.TensorChecks
