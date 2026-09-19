import RumocaCore.Real.Multiplication
import Mathlib.Tactic.FieldSimp

/-! Finite binary64 division, with exact-quotient rounding and signed zeros.
This is an authored IEEE numerical specification, not an assumption about Lean
Float or the host C compiler. The exact real quotient `value a / value b` is
rounded on the same integer-unit grid used by addition and multiplication:
scaling by the divisor's magnitude turns the quotient into the rational
`numerator / (scale * oneUnits)` that the scaled-rounding machinery rounds
without discarding fractional bits. Division by zero and overflow are rejected
by `divide?`; gradual underflow remains in domain and returns the signed zero.
Exception flags and traps are not modeled. The specification is noncomputable
and is never emitted as code. -/
namespace Rumoca.Binary64

set_option maxRecDepth 10000
set_option exponentiation.threshold 4096

/-- The exact quotient equals `numerator / (scale * oneUnits)` with
`scale = |units b|` and `numerator = units a * oneUnits * sign(units b)`. An
underflowed zero keeps the XOR of the operand signs. -/
noncomputable def roundedDiv (a b : Value) : Value :=
  let rounded := Scaled.round (units b).natAbs (units a * (oneUnits : Int) * (units b).sign)
  if units rounded = 0 then signedZero (negative a ^^ negative b) else rounded

theorem roundedDiv_canonical (a b : Value) :
    canonicalZero (roundedDiv a b) =
      Scaled.round (units b).natAbs (units a * (oneUnits : Int) * (units b).sign) := by
  dsimp only [roundedDiv]
  split
  · rw [canonicalZero_signedZero, Scaled.rounded_zero ‹_›]
  · simp only [canonicalZero, if_neg ‹_›]

theorem roundedDiv_zero_sign (a b : Value) (h : units (roundedDiv a b) = 0) :
    roundedDiv a b = signedZero (negative a ^^ negative b) := by
  by_cases hz : units (Scaled.round (units b).natAbs (units a * (oneUnits : Int) * (units b).sign)) = 0
  · simp only [roundedDiv, if_pos hz]
  · have : units (Scaled.round (units b).natAbs (units a * (oneUnits : Int) * (units b).sign)) = 0 := by
      simpa only [roundedDiv, if_neg hz] using h
    exact False.elim (hz this)

/-- Independent nearest/even quotient relation. Canonical rounding fixes the
numeric result; the second field fixes the operation's actual zero encoding. -/
structure QuotientRoundsNearestEven (a b result : Value) : Prop where
  rounded : Scaled.RoundsNearestEven (units b).natAbs
    (units a * (oneUnits : Int) * (units b).sign) (canonicalZero result)
  zero_sign : units result = 0 → result = signedZero (negative a ^^ negative b)

theorem roundedDiv_spec (a b : Value) : QuotientRoundsNearestEven a b (roundedDiv a b) := by
  refine ⟨?_, roundedDiv_zero_sign a b⟩
  rw [roundedDiv_canonical]
  exact Scaled.round_spec _ _

theorem quotient_rounding_unique (ha : QuotientRoundsNearestEven a b left)
    (hb : QuotientRoundsNearestEven a b right) : left = right := by
  have hc := Scaled.rounding_unique ha.rounded hb.rounded
  have hu : units left = units right := by
    simpa only [units_canonicalZero] using congrArg units hc
  by_cases hz : units left = 0
  · rw [ha.zero_sign hz, hb.zero_sign (hu.symm.trans hz)]
  · have hr : units right ≠ 0 := fun h => hz (hu.trans h)
    simpa only [canonicalZero, if_neg hz, if_neg hr] using hc

/-- Strict nearest-rounding overflow thresholds for the scaled quotient,
compared before rounding by exact integer cross-products. The divisor must be
nonzero for the quotient to be defined. -/
def finiteQuotient (a b : Value) : Prop :=
  units b ≠ 0 ∧
    -overflowUnits * (units b).natAbs < units a * (oneUnits : Int) * (units b).sign ∧
      units a * (oneUnits : Int) * (units b).sign < overflowUnits * (units b).natAbs

instance (a b : Value) : Decidable (finiteQuotient a b) := inferInstanceAs (Decidable (_ ∧ _))

noncomputable def divide? (a b : Value) : Option Value :=
  if finiteQuotient a b then some (roundedDiv a b) else none

def Divides (a b result : Value) : Prop := finiteQuotient a b ∧ QuotientRoundsNearestEven a b result

/-- The guarded operation accepts exactly the finite, nearest-even quotient
relation, including its zero sign. This characterizes every successful result. -/
theorem divide_correct (a b result : Value) : divide? a b = some result ↔ Divides a b result := by
  by_cases hd : finiteQuotient a b
  · simp only [divide?, Option.some.injEq, Divides, hd, if_true, true_and]
    exact ⟨fun h => h ▸ roundedDiv_spec a b, fun h => quotient_rounding_unique (roundedDiv_spec a b) h⟩
  · simp [divide?, Divides, hd]

theorem divide_complete (a b : Value) (h : finiteQuotient a b) :
    ∃ result, divide? a b = some result :=
  ⟨roundedDiv a b, (divide_correct _ _ _).mpr ⟨h, roundedDiv_spec a b⟩⟩

theorem roundedDiv_zero (a b : Value) (h : units a = 0) :
    roundedDiv a b = signedZero (negative a ^^ negative b) := by
  have hz : units positiveZero = 0 := by decide +kernel
  simp [roundedDiv, h, Scaled.round_zero, hz]

/-- The scaled integer quotient recovers the exact real quotient once the
divisor is nonzero: the divisor's sign and magnitude reproduce `value a / value b`. -/
private theorem quotient_scale (a b : Value) (hb : units b ≠ 0) :
    ((units a * (oneUnits : Int) * (units b).sign : Int) : ℝ) /
        (((units b).natAbs : ℝ) * (oneUnits : ℝ)) = value a / value b := by
  have ho : (oneUnits : ℝ) ≠ 0 := ne_of_gt oneUnits_real_pos
  have hd : (units b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hs0 : (units b).sign ≠ 0 := by
    intro h0
    have h := Int.sign_mul_self_eq_natAbs (units b)
    rw [h0, zero_mul] at h
    omega
  have hs : ((units b).sign : ℝ) ≠ 0 := by exact_mod_cast hs0
  have hA : ((units b).natAbs : ℝ) = ((units b).sign : ℝ) * (units b : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.sign_mul_self_eq_natAbs (units b))
    simp only [Int.cast_mul, Int.cast_natCast] at h
    exact h.symm
  rw [hA, value, value]
  push_cast
  field_simp

/-- A Real nearest-value result: the rounded quotient is at least as close to
the exact quotient as any representable candidate, for every nonzero divisor. -/
theorem roundedDiv_nearest (a b candidate : Value) (hb : units b ≠ 0) :
    |value (roundedDiv a b) - value a / value b| ≤ |value candidate - value a / value b| := by
  have positive : 0 < (units b).natAbs := Int.natAbs_pos.mpr hb
  have h := Scaled.round_nearest (units b).natAbs positive
    (units a * (oneUnits : Int) * (units b).sign) candidate
  rw [quotient_scale a b hb, ← roundedDiv_canonical, value_canonicalZero] at h
  exact h

theorem roundedDiv_exact (a b candidate : Value) (hb : units b ≠ 0)
    (h : value candidate = value a / value b) : value (roundedDiv a b) = value a / value b := by
  have he := roundedDiv_nearest a b candidate hb
  rw [h, sub_self, abs_zero] at he
  exact sub_eq_zero.mp (abs_nonpos_iff.mp he)

/-- Any representable bracket bounds the quotient error by half its width. -/
theorem roundedDiv_half_spacing (a b lo hi : Value) (hb : units b ≠ 0)
    (hl : value lo ≤ value a / value b) (hh : value a / value b ≤ value hi) :
    |value (roundedDiv a b) - value a / value b| ≤ (value hi - value lo) / 2 := by
  have ha := roundedDiv_nearest a b lo hb
  have hc := roundedDiv_nearest a b hi hb
  rw [abs_of_nonpos (show value lo - value a / value b ≤ 0 by linarith)] at ha
  rw [abs_of_nonneg (show 0 ≤ value hi - value a / value b by linarith)] at hc
  linarith

/-- The integer guard is exactly the open nearest-rounding interval around
zero in Real units, once the divisor is nonzero. Crossing either threshold is
rejected, not saturated. -/
theorem finiteQuotient_real (a b : Value) : finiteQuotient a b ↔
    units b ≠ 0 ∧ -(overflowUnits : ℝ) / oneUnits < value a / value b ∧
      value a / value b < (overflowUnits : ℝ) / oneUnits := by
  unfold finiteQuotient
  apply and_congr_right
  intro hb
  have hp := oneUnits_real_pos
  have hAr : (0 : ℝ) < ((units b).natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hb
  have hscale : (0 : ℝ) < ((units b).natAbs : ℝ) * oneUnits := mul_pos hAr hp
  have hl : (-(overflowUnits : ℝ) / oneUnits) * (((units b).natAbs : ℝ) * oneUnits) =
      -(overflowUnits : ℝ) * ((units b).natAbs : ℝ) := by
    rw [mul_comm ((units b).natAbs : ℝ) (oneUnits : ℝ), ← mul_assoc,
      div_mul_cancel₀ _ (ne_of_gt oneUnits_real_pos)]
  have hh : ((overflowUnits : ℝ) / oneUnits) * (((units b).natAbs : ℝ) * oneUnits) =
      (overflowUnits : ℝ) * ((units b).natAbs : ℝ) := by
    rw [mul_comm ((units b).natAbs : ℝ) (oneUnits : ℝ), ← mul_assoc,
      div_mul_cancel₀ _ (ne_of_gt oneUnits_real_pos)]
  have hcl : -(overflowUnits : ℝ) * ((units b).natAbs : ℝ) =
      ((-overflowUnits * (units b).natAbs : Int) : ℝ) := by
    rw [Int.cast_mul, Int.cast_neg, Int.cast_natCast]
  have hch : (overflowUnits : ℝ) * ((units b).natAbs : ℝ) =
      ((overflowUnits * (units b).natAbs : Int) : ℝ) := by
    rw [Int.cast_mul, Int.cast_natCast]
  rw [← quotient_scale a b hb, lt_div_iff₀ hscale, div_lt_iff₀ hscale, hl, hh, hcl, hch,
    Int.cast_lt, Int.cast_lt]

end Rumoca.Binary64
