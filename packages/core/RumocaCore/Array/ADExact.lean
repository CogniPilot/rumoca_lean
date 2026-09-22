import RumocaCore.Array.Finite
import RumocaCore.Real.Comparison
import RumocaCore.Real.AdditionResult

/-! Exact finite AD/materializer connection. No compiler rewrite:
ordered program execution and its unused primal multiplication stay explicit. -/
noncomputable section
namespace Rumoca.Binary64.ADExact
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096

theorem units_zero_cases (x : Value) (zero : units x = 0) :
    x = positiveZero ∨ x = negativeZero := by
  have magnitude : magnitudeUnits x = 0 := by
    unfold units at zero
    split at zero <;> omega
  have coefficient : (if exponent x = 0 then fraction x else fractionCount + fraction x) = 0 := by
    exact (Nat.mul_eq_zero.mp magnitude).resolve_right (ne_of_gt (Nat.two_pow_pos _))
  have exp_zero : exponent x = 0 := by
    by_contra nonzero
    rw [if_neg nonzero] at coefficient
    have positive : 0 < fractionCount := by decide +kernel
    omega
  have frac_zero : fraction x = 0 := by simpa only [if_pos exp_zero] using coefficient
  have code_zero : magnitudeCode x = 0 := by
    simp only [exponent, fractionCount] at exp_zero
    simp only [fraction, fractionCount] at frac_zero
    omega
  have bound := x.isLt
  simp only [magnitudeCode] at code_zero
  simp only [count] at bound
  have choices : x.val = 0 ∨ x.val = magnitudeCount := by
    simp only [magnitudeCount, fractionCount] at code_zero bound ⊢
    omega
  rcases choices with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

theorem roundedMul_one_units (x : Value) : units (roundedMul x one) = units x := by
  apply (Float64.value_eq_iff _ _).1
  simpa only [value_one, mul_one] using
    roundedMul_exact x one x (by rw [value_one, mul_one])

theorem roundedMul_one_negative_zero (x : Value) :
    roundedMul x one = negativeZero ↔ x = negativeZero := by
  have negative_one : negative one = false := by decide +kernel
  have positive_sign : negative positiveZero = false := by decide +kernel
  have negative_sign : negative negativeZero = true := by decide +kernel
  have zero_positive : units positiveZero = 0 := by decide +kernel
  have zero_negative : units negativeZero = 0 := by decide +kernel
  constructor
  · intro equal
    have zero : units x = 0 := by rw [← roundedMul_one_units x, equal, zero_negative]
    rcases units_zero_cases x zero with rfl | rfl
    · have rounded := roundedMul_zero positiveZero one (by rw [zero_positive, zero_mul])
      simp only [positive_sign, negative_one, Bool.xor_false, signedZero, Bool.false_eq_true,
        if_false] at rounded
      have impossible : positiveZero = negativeZero := rounded.symm.trans equal
      have distinct : positiveZero ≠ negativeZero := by decide +kernel
      exact False.elim (distinct impossible)
    · rfl
  · rintro rfl
    have rounded := roundedMul_zero negativeZero one (by rw [zero_negative, zero_mul])
    simpa only [negative_sign, negative_one, Bool.xor_false, signedZero, if_true] using rounded

/-- Addition depends on exact units and the negative-zero case, not on real
value equality alone. These hypotheses preserve its result encoding exactly. -/
theorem roundedAdd_congr (a b c d : Value)
    (left : units a = units c) (right : units b = units d)
    (left_zero : a = negativeZero ↔ c = negativeZero)
    (right_zero : b = negativeZero ↔ d = negativeZero) :
    roundedAdd a b = roundedAdd c d := by
  simp only [roundedAdd, left, right, left_zero, right_zero]

theorem doubled_unit_products (x : Value) :
    roundedAdd (roundedMul x one) (roundedMul x one) = roundedAdd x x :=
  roundedAdd_congr _ _ _ _ (roundedMul_one_units x) (roundedMul_one_units x)
    (roundedMul_one_negative_zero x) (roundedMul_one_negative_zero x)

theorem finiteProduct_one (x : Value) : finiteProduct x one := by
  have bounds := units_bound x
  have positive : (0 : Int) < oneUnits := by exact_mod_cast oneUnits_pos
  have margin : (0 : Int) < 2 ^ 2044 := by positivity
  have lower : -overflowUnits < units x := by unfold overflowUnits; omega
  have upper : units x < overflowUnits := by unfold overflowUnits; omega
  simpa only [finiteProduct, units_one, neg_mul] using
    And.intro (mul_lt_mul_of_pos_right lower positive) (mul_lt_mul_of_pos_right upper positive)

end Rumoca.Binary64.ADExact

namespace Rumoca.ArrayProfile.ADExact
open Rumoca.Tensor Solve.Tensor

/-- Domain characterization keeps the primal square, despite its result being
unused by the tangent projection. Products with the unit tangent are finite;
the final addition still needs its strict finite overflow interval. -/
theorem coefficients_domain (state input : Value Binary64.Value shape) :
    Finite.InDomain (squareJacobianProgram shape).coefficients (environment state input) ↔
      (∀ i : Fin shape.volume, Binary64.finiteProduct input[i] input[i]) ∧
      (∀ i : Fin shape.volume, Finite.Domain .add input[i] input[i]) := by
  simp only [squareJacobianProgram, squareProgram, Program.forward, Finite.InDomain,
    environment, Literal.eval, Env.push, Ren.push, Fin.getElem_fin, Value.getElem_fill,
    BinaryOp.eval, Value.getElem_zipWith, BinaryOp.scalar, Finite.ops, Finite.Domain,
    Binary64.ADExact.roundedMul_one_units, Binary64.ADExact.finiteProduct_one,
    and_true, true_and, forall_true_iff]

theorem coefficients_eval_get (state input : Value Binary64.Value shape) (i : Fin shape.volume) :
    ((squareJacobianProgram shape).coefficients.eval Finite.ops
      Binary64.positiveZero Binary64.one (environment state input))[i] =
      Binary64.roundedAdd input[i] input[i] := by
  rw [square_coefficients_eval]
  simp only [BinaryOp.jvp, BinaryOp.eval, BinaryOp.scalar, Finite.ops,
    Fin.getElem_fin, Value.getElem_zipWith, Value.getElem_fill]
  exact Binary64.ADExact.doubled_unit_products _

/-- Exact encoding equality of completed ordered AD coefficients and the
scratch-free doubled-input vector. Execution of all AD instructions remains
an explicit premise, including the otherwise unused primal square. -/
theorem coefficients_exact (state input result : Value Binary64.Value shape)
    (executed : Finite.Executes (squareJacobianProgram shape).coefficients
      (environment state input) result) (i : Fin shape.volume) :
    result[i] = Binary64.roundedAdd input[i] input[i] := by
  rw [square_jacobian_coefficients_finite state input result executed i,
    Binary64.ADExact.doubled_unit_products]

/-- Exact finite behavior, not just nearestness: the ordered AD program
executes precisely when its primal square and the materializer's additions are
finite, and its result has the SAME finite encodings (including signed zero).
The primal condition cannot be omitted merely because the tangent is returned. -/
theorem coefficients_executes_iff (state input result : Value Binary64.Value shape) :
    Finite.Executes (squareJacobianProgram shape).coefficients (environment state input) result ↔
      (∀ i : Fin shape.volume, Binary64.finiteProduct input[i] input[i]) ∧
      (∀ i : Fin shape.volume, Binary64.Adds input[i] input[i] (.finite result[i])) := by
  constructor
  · intro executed
    have domain := (coefficients_domain state input).1 (Finite.executes_sound executed).1
    refine ⟨domain.1, ?_⟩
    intro i
    refine ⟨(Binary64.sum_above_negative_overflow _ _).2 (domain.2 i).1,
      (Binary64.sum_below_overflow _ _).2 (domain.2 i).2, ?_⟩
    rw [coefficients_exact state input result executed i]
    exact Binary64.roundedAdd_spec _ _
  · rintro ⟨primal, adds⟩
    apply (Finite.executes_iff _ _ _).2
    refine ⟨(coefficients_domain state input).2 ⟨primal, ?_⟩, ?_⟩
    · intro i
      exact ⟨(Binary64.sum_above_negative_overflow _ _).1 (adds i).1,
        (Binary64.sum_below_overflow _ _).1 (adds i).2.1⟩
    · apply Value.ext
      intro i hi
      exact (Binary64.sum_rounding_unique (adds ⟨i, hi⟩).2.2
        (Binary64.roundedAdd_spec _ _)).trans (coefficients_eval_get state input ⟨i, hi⟩).symm

end Rumoca.ArrayProfile.ADExact
