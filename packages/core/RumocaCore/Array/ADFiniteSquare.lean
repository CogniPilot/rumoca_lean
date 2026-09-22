import RumocaCore.Array.ADExact

/-! The square RHS domain suffices for its ordered forward derivative.
This removes a redundant addition-domain premise, not primal overflow checks.
All equalities below preserve finite encodings, including signed zero. -/
noncomputable section
namespace Rumoca.Binary64.ADExact
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096

/-- A finite square leaves enough exponent range for doubling its operand. -/
theorem finite_square_doubling (x : Value) (finite : finiteProduct x x) :
    -overflowUnits < units x + units x ∧ units x + units x < overflowUnits := by
  have positive : (0 : Int) < overflowUnits := by decide +kernel
  have room : (4 : Int) * oneUnits < overflowUnits := by decide +kernel
  have gap : 0 < overflowUnits * (overflowUnits - 4 * oneUnits) :=
    mul_pos positive (by omega)
  have upper := finite.2
  constructor
  · by_contra outside
    have lower : 0 ≤ -2 * units x - overflowUnits := by omega
    have other : 0 ≤ -2 * units x + overflowUnits := by omega
    have square := mul_nonneg lower other
    nlinarith
  · by_contra outside
    have lower : 0 ≤ 2 * units x - overflowUnits := by omega
    have other : 0 ≤ 2 * units x + overflowUnits := by omega
    have square := mul_nonneg lower other
    nlinarith

theorem adds_self_of_finite_square (x : Value) (finite : finiteProduct x x) :
    Adds x x (.finite (roundedAdd x x)) :=
  ⟨(sum_above_negative_overflow x x).2 (finite_square_doubling x finite).1,
    (sum_below_overflow x x).2 (finite_square_doubling x finite).2,
    roundedAdd_spec x x⟩

end Rumoca.Binary64.ADExact

namespace Rumoca.ArrayProfile.ADExact
open Rumoca.Tensor Solve.Tensor

/-- Includes the unused primal multiplication in the ordered AD program. -/
theorem coefficients_domain_iff_square (state input : Value Binary64.Value shape) :
    Finite.InDomain (squareJacobianProgram shape).coefficients (environment state input) ↔
      ∀ i : Fin shape.volume, Binary64.finiteProduct input[i] input[i] := by
  rw [coefficients_domain]
  exact ⟨And.left, fun primal =>
    ⟨primal, fun i => Binary64.ADExact.finite_square_doubling _ (primal i)⟩⟩

theorem coefficients_from_finite_rhs (state input rhs : Value Binary64.Value shape)
    (executed : Finite.Executes (squareProgram shape) (environment state input) rhs) :
    Finite.Executes (squareJacobianProgram shape).coefficients (environment state input)
      ((squareJacobianProgram shape).coefficients.eval Finite.ops
        Binary64.positiveZero Binary64.one (environment state input)) := by
  apply Finite.execute_of_domain
  exact (coefficients_domain_iff_square state input).2
    (fun i => ((square_finite_correct state input rhs).1 executed i).1)

/-- The materializer's additions are consequences of RHS execution, with no
independent choice of rounded result or additional numerical assumption. -/
theorem coefficient_adds_from_finite_rhs (state input rhs : Value Binary64.Value shape)
    (executed : Finite.Executes (squareProgram shape) (environment state input) rhs)
    (i : Fin shape.volume) :
    Binary64.Adds input[i] input[i]
      (.finite (((squareJacobianProgram shape).coefficients.eval Finite.ops
        Binary64.positiveZero Binary64.one (environment state input))[i])) := by
  rw [coefficients_eval_get]
  exact Binary64.ADExact.adds_self_of_finite_square _
    (((square_finite_correct state input rhs).1 executed i).1)

end Rumoca.ArrayProfile.ADExact
