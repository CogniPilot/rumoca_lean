import RumocaCore.Array.ADExact
import RumocaC.SquareJacobianObservation

noncomputable section
namespace Rumoca.CTensor.SquareJacobianExact
open CMemory CMemory.TensorView Rumoca.Tensor Solve.Tensor

/-- Exact coefficient encodings follow from the helper's independent Adds
relation and the signed-zero-aware ordered AD evaluator theorem. -/
theorem coefficients_equal (state input result : Values shape)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds input[i] input[i] (.finite result[i])) :
    result = (ArrayProfile.squareJacobianProgram shape).coefficients.eval Finite.ops
      Binary64.positiveZero Binary64.one (ArrayProfile.environment state input) := by
  apply Value.ext
  intro i hi
  exact (Binary64.sum_rounding_unique (adds ⟨i, hi⟩).2.2
    (Binary64.roundedAdd_spec _ _)).trans
    (ArrayProfile.ADExact.coefficients_eval_get state input ⟨i, hi⟩).symm

theorem matrix_equal (state input result : Values shape)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds input[i] input[i] (.finite result[i])) :
    Diagonal.matrix result = (ArrayProfile.squareJacobianProgram shape).eval Finite.ops
      Binary64.positiveZero Binary64.one (ArrayProfile.environment state input) := by
  rw [coefficients_equal state input result adds]
  exact Diagonal.solve_matrix _ _

/-- A successful RHS supplies the primal square's finite-domain obligation.
The two unit-tangent multiplications are proved finite, not assumed away. -/
theorem coefficients_from_rhs (state input rhs result : Values shape)
    (executed : Finite.Executes (ArrayProfile.squareProgram shape)
      (ArrayProfile.environment state input) rhs)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds input[i] input[i] (.finite result[i])) :
    Finite.Executes (ArrayProfile.squareJacobianProgram shape).coefficients
      (ArrayProfile.environment state input) result :=
  (ArrayProfile.ADExact.coefficients_executes_iff state input result).2
    ⟨fun i => ((ArrayProfile.square_finite_correct state input rhs).1 executed i).1, adds⟩

end Rumoca.CTensor.SquareJacobianExact
