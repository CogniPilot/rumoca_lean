import RumocaCore.Real.AdditionResult
import RumocaCore.Real.IntegerConversion

/-! Finite binary64 subtraction under round-to-nearest-even. The exact real
difference is rounded on the same integer-unit grid as addition. Negation is
exact, so rounded subtraction equals rounded addition of the exact negation;
this file proves that relation rather than assuming it. Signed zero follows the
subtraction rule: the only negative-zero result is `(-0) - (+0)`. Overflow
yields signed infinity; NaN is never produced from finite operands. Exception
flags and traps are outside this numerical relation. -/

set_option maxRecDepth 10000
set_option exponentiation.threshold 4096

namespace Rumoca.Binary64
open Rumoca.Float64

/-- The sole negative-zero difference is `(-0) - (+0)`; every other exact-zero
difference is the canonical positive zero from nearest/even rounding. -/
noncomputable def roundedSub (a b : Value) : Value :=
  if a = negativeZero ∧ b = positiveZero then negativeZero else round (units a - units b)

theorem roundedSub_negative_zero : roundedSub negativeZero positiveZero = negativeZero := by
  simp only [roundedSub, and_self, if_true]

theorem negate_positiveZero : negate positiveZero = negativeZero := by decide +kernel

theorem negate_negativeZero : negate negativeZero = positiveZero := by decide +kernel

/-- Closed form for the encoding of a negation. -/
theorem negate_val (x : Value) :
    (negate x).val =
      if x.val < magnitudeCount then x.val + magnitudeCount else x.val - magnitudeCount := by
  unfold negate
  by_cases h : x.val < magnitudeCount
  · rw [dif_pos h, if_pos h]
  · rw [dif_neg h, if_neg h]

/-- Negation is an involution on the finite encoding. -/
theorem negate_negate (x : Value) : negate (negate x) = x := by
  have bound := x.isLt
  unfold count at bound
  apply Fin.ext
  simp only [negate_val]
  split_ifs <;> omega

theorem negate_eq_negativeZero (b : Value) : negate b = negativeZero ↔ b = positiveZero := by
  constructor
  · intro h
    have := congrArg negate h
    simpa only [negate_negate, negate_negativeZero] using this
  · rintro rfl; exact negate_positiveZero

/-- Rounded subtraction is rounded addition of the exact negation, since
negation is a sign flip with no rounding. -/
theorem roundedSub_eq_add_negate (a b : Value) : roundedSub a b = roundedAdd a (negate b) := by
  unfold roundedSub roundedAdd
  have hcond : (a = negativeZero ∧ b = positiveZero) ↔ (a = negativeZero ∧ negate b = negativeZero) := by
    rw [negate_eq_negativeZero]
  by_cases h : a = negativeZero ∧ b = positiveZero
  · rw [if_pos h, if_pos (hcond.mp h)]
  · rw [if_neg h, if_neg (fun hb => h (hcond.mpr hb)),
      show units a + units (negate b) = units a - units b from by rw [negate_units]; ring]

theorem roundedSub_positive_zero : roundedSub positiveZero positiveZero = positiveZero := by
  have hn : ¬ (positiveZero = negativeZero ∧ positiveZero = positiveZero) := by
    rintro ⟨h, _⟩; exact absurd h (by decide +kernel)
  have hu : units positiveZero = 0 := by decide +kernel
  rw [roundedSub, if_neg hn, hu, sub_zero, round_zero]

/-- Signed-zero-aware subtraction rounding. The ordinary nearest/even relation
fixes every other result independently of the chosen rounding implementation. -/
def DifferenceRoundsNearestEven (a b result : Value) : Prop :=
  if a = negativeZero ∧ b = positiveZero then result = negativeZero
  else RoundsNearestEven (units a - units b) result

theorem roundedSub_spec (a b : Value) : DifferenceRoundsNearestEven a b (roundedSub a b) := by
  unfold DifferenceRoundsNearestEven roundedSub
  split
  · rfl
  · exact round_spec _

theorem difference_rounding_unique (first : DifferenceRoundsNearestEven a b x)
    (second : DifferenceRoundsNearestEven a b y) : x = y := by
  by_cases zero : a = negativeZero ∧ b = positiveZero
  · rw [DifferenceRoundsNearestEven, if_pos zero] at first second
    exact first.trans second.symm
  · rw [DifferenceRoundsNearestEven, if_neg zero] at first second
    exact rounding_unique first second

/-- Nearest-value error bound for the rounded difference, including the
subnormal range and the signed-zero case. -/
theorem roundedSub_nearest (a b candidate : Value) :
    |value (roundedSub a b) - (value a - value b)| ≤ |value candidate - (value a - value b)| := by
  by_cases hz : a = negativeZero ∧ b = positiveZero
  · obtain ⟨rfl, rfl⟩ := hz
    have hun : units negativeZero = 0 := by decide +kernel
    have hup : units positiveZero = 0 := by decide +kernel
    have hvn : value negativeZero = 0 := by simp only [value, hun, Int.cast_zero, zero_div]
    have hvp : value positiveZero = 0 := by simp only [value, hup, Int.cast_zero, zero_div]
    rw [roundedSub_negative_zero, hvn, hvp, sub_zero, sub_zero, abs_zero]
    exact abs_nonneg _
  · have h := Scaled.round_nearest 1 (by decide) (units a - units b) candidate
    have he : ((units a - units b : Int) : ℝ) / ((1 : Nat) * oneUnits) = value a - value b := by
      simp only [Int.cast_sub, Nat.cast_one, one_mul, sub_div, value]
    rw [Scaled.round_one, he] at h
    simpa only [roundedSub, if_neg hz] using h

theorem roundedSub_exact (a b candidate : Value) (h : value candidate = value a - value b) :
    value (roundedSub a b) = value a - value b := by
  have he := roundedSub_nearest a b candidate
  rw [h, sub_self, abs_zero] at he
  exact sub_eq_zero.mp (abs_nonpos_iff.mp he)

end Rumoca.Binary64

namespace Rumoca.Binary64
open Rumoca.Float64
noncomputable section

theorem difference_below_overflow (a b : Value) :
    value a - value b < overflowValue ↔ units a - units b < overflowUnits := by
  unfold value overflowValue
  rw [← sub_div, div_lt_div_iff_of_pos_right oneUnits_real_pos]
  exact_mod_cast Iff.rfl

theorem difference_above_negative_overflow (a b : Value) :
    -overflowValue < value a - value b ↔ -overflowUnits < units a - units b := by
  unfold value overflowValue
  rw [← neg_div, ← sub_div, div_lt_div_iff_of_pos_right oneUnits_real_pos]
  exact_mod_cast Iff.rfl

/-- Independent result relation for any pair of finite operands. Threshold
ties overflow in nearest-even mode; a finite-input subtraction never yields NaN. -/
def Subtracts (a b : Value) : Number → Prop
  | .negativeInfinity => value a - value b ≤ -overflowValue
  | .positiveInfinity => overflowValue ≤ value a - value b
  | .finite result => -overflowValue < value a - value b ∧
      value a - value b < overflowValue ∧ DifferenceRoundsNearestEven a b result
  | .nan => False

/-- Total numerical subtraction of finite operands under nearest-even rounding.
This semantic function is not executed by the production compiler. -/
def subResult (a b : Value) : Number :=
  if units a - units b ≤ -overflowUnits then .negativeInfinity
  else if overflowUnits ≤ units a - units b then .positiveInfinity
  else .finite (roundedSub a b)

theorem subResult_spec (a b : Value) : Subtracts a b (subResult a b) := by
  unfold subResult
  split
  · change value a - value b ≤ -overflowValue
    exact le_of_not_gt (fun h => not_lt_of_ge ‹_› ((difference_above_negative_overflow a b).mp h))
  · split
    · change overflowValue ≤ value a - value b
      exact le_of_not_gt (fun h => not_lt_of_ge ‹_› ((difference_below_overflow a b).mp h))
    · exact ⟨(difference_above_negative_overflow a b).mpr (lt_of_not_ge ‹_›),
        (difference_below_overflow a b).mpr (lt_of_not_ge ‹_›), roundedSub_spec a b⟩

theorem subtracts_unique (first : Subtracts a b x) (second : Subtracts a b y) : x = y := by
  have positive := overflowValue_pos
  cases x <;> cases y <;> simp only [Subtracts] at first second
  all_goals try rfl
  case finite.finite x y => exact congrArg Number.finite (difference_rounding_unique first.2.2 second.2.2)
  all_goals
    try obtain ⟨lower, upper, _⟩ := first
    try obtain ⟨lower', upper', _⟩ := second
    exfalso
    linarith

theorem subResult_correct (a b : Value) (result : Number) :
    subResult a b = result ↔ Subtracts a b result :=
  ⟨fun same => same ▸ subResult_spec a b, fun spec => subtracts_unique (subResult_spec a b) spec⟩

theorem subResult_finite (a b : Value)
    (bounded : -overflowUnits < units a - units b ∧ units a - units b < overflowUnits) :
    subResult a b = .finite (roundedSub a b) := by
  simp only [subResult, if_neg (not_le_of_gt bounded.1), if_neg (not_le_of_gt bounded.2)]

theorem subResult_no_nan (a b : Value) : subResult a b ≠ .nan := by
  intro same
  exact (subResult_correct a b .nan).mp same

/-- The Number-level subtraction is the addition of the exact negation. -/
theorem subResult_eq_addResult_negate (a b : Value) : subResult a b = addResult a (negate b) := by
  have hu : units a + units (negate b) = units a - units b := by rw [negate_units]; omega
  unfold subResult addResult
  rw [hu, roundedSub_eq_add_negate]

end
end Rumoca.Binary64
