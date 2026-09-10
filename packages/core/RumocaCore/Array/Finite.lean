import RumocaCore.Array.Lowering
import RumocaCore.Solve.Tensor.Finite
import RumocaCore.Real.Addition

/-! Finite execution and Real error contracts for the actual array square
and AD-generated Jacobian programs. These are instantaneous Solve contracts;
C loops, FMI lifecycles and time discretization remain separate obligations. -/
noncomputable section
namespace Rumoca.ArrayProfile
open Rumoca.Tensor Solve.Tensor

theorem square_finite_correct (state input result : Value Binary64.Value shape) :
    Finite.Executes (squareProgram shape) (environment state input) result ↔
      ∀ i : Fin shape.volume, Binary64.Multiplies input[i] input[i] result[i] := by
  rw [Finite.executes_iff]
  simpa only [squareProgram, Finite.InDomain, Program.eval, environment, Env.push, and_true,
    Finite.Pointwise, Finite.Result, Finite.Domain, Binary64.Multiplies] using
      (Finite.pointwise_iff .mul input input result).symm

/-- Each returned derivative is a nearest finite value to the mathematical
source RHS. This relates the ordered finite program to the Real square. -/
theorem square_finite_nearest (state input result : Value Binary64.Value shape)
    (executed : Finite.Executes (squareProgram shape) (environment state input) result)
    (i : Fin shape.volume) (candidate : Binary64.Value) :
    |Binary64.value result[i] - Binary64.value input[i] * Binary64.value input[i]| ≤
      |Binary64.value candidate - Binary64.value input[i] * Binary64.value input[i]| := by
  have h := ((square_finite_correct state input result).mp executed i).2
  rw [Binary64.product_rounding_unique h (Binary64.roundedMul_spec _ _)]
  exact Binary64.roundedMul_nearest _ _ _

/-- Execution retains the two ordered product contributions emitted by AD.
No simplification to `2*u` is inserted in either the compiler or the backend. -/
theorem square_jacobian_coefficients_finite (state input result : Value Binary64.Value shape)
    (executed : Finite.Executes (squareJacobianProgram shape).coefficients
      (environment state input) result) (i : Fin shape.volume) :
    result[i] = Binary64.roundedAdd (Binary64.roundedMul input[i] Binary64.one)
      (Binary64.roundedMul input[i] Binary64.one) := by
  rw [(Finite.executes_sound executed).2, square_coefficients_eval]
  simp only [Fin.getElem_fin, BinaryOp.jvp, BinaryOp.eval, Value.getElem_zipWith, Value.getElem_fill,
    BinaryOp.scalar, Finite.ops]

/-- The AD coefficient is nearest to the corresponding Real derivative.
Multiplication by one is exact in value; addition supplies the final rounding.
This is not a derivative of the discontinuous machine-rounding function. -/
theorem square_jacobian_coefficients_nearest (state input result : Value Binary64.Value shape)
    (executed : Finite.Executes (squareJacobianProgram shape).coefficients
      (environment state input) result) (i : Fin shape.volume) (candidate : Binary64.Value) :
    |Binary64.value result[i] - 2 * Binary64.value input[i]| ≤
      |Binary64.value candidate - 2 * Binary64.value input[i]| := by
  have exact_one : Binary64.value (Binary64.roundedMul input[i] Binary64.one) = Binary64.value input[i] := by
    simpa only [Binary64.value_one, mul_one] using Binary64.roundedMul_exact input[i] Binary64.one input[i]
      (by rw [Binary64.value_one, mul_one])
  rw [square_jacobian_coefficients_finite state input result executed i]
  have h := Binary64.roundedAdd_nearest (Binary64.roundedMul input[i] Binary64.one)
    (Binary64.roundedMul input[i] Binary64.one) candidate
  simpa only [exact_one, two_mul] using h

end Rumoca.ArrayProfile
