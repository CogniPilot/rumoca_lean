import RumocaCore.Array.Finite
import RumocaCore.Solve.Tensor.Numerical

/-! Exact finite-refinement boundary of the existing square Solve program.
The encoded detector does not mistake overflowing real products for finite
derivatives. This is not a runtime status policy or complete source trajectory. -/
noncomputable section
namespace Rumoca.ArrayProfile
open Rumoca.Tensor Solve.Tensor
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096

theorem square_detection_finite_execution (state input : Value Binary64.Value shape) :
    Numerical.allFiniteBits (Numerical.encode (Numerical.multiply input input)) = true ↔
      ∃ result, Finite.Executes (squareProgram shape) (environment state input) result := by
  rw [Numerical.allFiniteBits_encode, Numerical.multiply_allFinite_iff]
  constructor
  · intro bounded
    refine ⟨input.zipWith Binary64.roundedMul input, (square_finite_correct _ _ _).2 ?_⟩
    intro i
    exact ⟨bounded i, by
      simpa only [Fin.getElem_fin, Value.getElem_zipWith] using
        Binary64.roundedMul_spec input[i] input[i]⟩
  · rintro ⟨result, executed⟩ i
    exact ((square_finite_correct state input result).1 executed i).1

/-- Failure has an exact independent real overflow witness at a coordinate;
there is no NaN or negative-square-infinity alternative for finite inputs. -/
theorem square_detection_overflow (input : Value Binary64.Value shape) :
    Numerical.allFiniteBits (Numerical.encode (Numerical.multiply input input)) = false ↔
      ∃ i : Fin shape.volume,
        Binary64.overflowValue ≤ Binary64.value input[i] * Binary64.value input[i] := by
  rw [Numerical.multiply_detects_iff]
  apply exists_congr
  intro i
  rw [Binary64.finiteProduct_real]
  have nonnegative := mul_self_nonneg (Binary64.value input[i])
  have positive := Binary64.overflowValue_pos
  simp only [Binary64.overflowValue, neg_div] at *
  constructor
  · intro outside
    by_contra below
    exact outside ⟨by linarith, by linarith⟩
  · intro above bounded
    exact not_lt_of_ge above bounded.2

end Rumoca.ArrayProfile
