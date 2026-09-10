import RumocaCore.Real.ScaledRounding

/-! Finite binary64 multiplication, with exact product rounding and signed
zeros. This is an authored IEEE numerical specification, not an assumption
about Lean Float or the host C compiler. Overflow is rejected by `multiply?`;
gradual underflow remains in domain. Exception flags and traps are not modeled.
The arithmetic specification is noncomputable and is never emitted as code. -/
namespace Rumoca.Binary64

def signedZero (sign : Bool) : Value := if sign then negativeZero else positiveZero

def canonicalZero (x : Value) : Value := if units x = 0 then positiveZero else x

theorem units_signedZero (sign : Bool) : units (signedZero sign) = 0 := by
  cases sign <;> decide +kernel

theorem units_canonicalZero (x : Value) : units (canonicalZero x) = units x := by
  have hz : units positiveZero = 0 := by decide +kernel
  unfold canonicalZero
  split
  · simpa only [hz] using (‹units x = 0›).symm
  · rfl

theorem canonicalZero_signedZero (sign : Bool) : canonicalZero (signedZero sign) = positiveZero := by
  simp [canonicalZero, units_signedZero]

theorem value_canonicalZero (x : Value) : value (canonicalZero x) = value x := by
  simp only [value, units_canonicalZero]

/-- The exact product has denominator `oneUnits` when expressed in units of
2^-1074. An underflowed zero keeps the XOR of the operand signs. -/
noncomputable def roundedMul (a b : Value) : Value :=
  let rounded := Scaled.round oneUnits (units a * units b)
  if units rounded = 0 then signedZero (negative a ^^ negative b) else rounded

theorem roundedMul_canonical (a b : Value) :
    canonicalZero (roundedMul a b) = Scaled.round oneUnits (units a * units b) := by
  dsimp only [roundedMul]
  split
  · rw [canonicalZero_signedZero, Scaled.rounded_zero ‹_›]
  · simp only [canonicalZero, if_neg ‹_›]

theorem roundedMul_zero_sign (a b : Value) (h : units (roundedMul a b) = 0) :
    roundedMul a b = signedZero (negative a ^^ negative b) := by
  by_cases hz : units (Scaled.round oneUnits (units a * units b)) = 0
  · simp only [roundedMul, if_pos hz]
  · have : units (Scaled.round oneUnits (units a * units b)) = 0 := by
      simpa only [roundedMul, if_neg hz] using h
    exact False.elim (hz this)

/-- Independent nearest/even product relation. Canonical rounding fixes the
numeric result; the second field fixes the operation's actual zero encoding. -/
structure ProductRoundsNearestEven (a b result : Value) : Prop where
  rounded : Scaled.RoundsNearestEven oneUnits (units a * units b) (canonicalZero result)
  zero_sign : units result = 0 → result = signedZero (negative a ^^ negative b)

theorem roundedMul_spec (a b : Value) : ProductRoundsNearestEven a b (roundedMul a b) := by
  refine ⟨?_, roundedMul_zero_sign a b⟩
  rw [roundedMul_canonical]
  exact Scaled.round_spec _ _

theorem product_rounding_unique (ha : ProductRoundsNearestEven a b left)
    (hb : ProductRoundsNearestEven a b right) : left = right := by
  have hc := Scaled.rounding_unique ha.rounded hb.rounded
  have hu : units left = units right := by
    simpa only [units_canonicalZero] using congrArg units hc
  by_cases hz : units left = 0
  · rw [ha.zero_sign hz, hb.zero_sign (hu.symm.trans hz)]
  · have hr : units right ≠ 0 := fun h => hz (hu.trans h)
    simpa only [canonicalZero, if_neg hz, if_neg hr] using hc

/-- Strict nearest-rounding overflow thresholds, compared before rounding
by exact integer cross-products. No integer quotient truncates a small product. -/
def overflowUnits : Int := maxUnits + 2 ^ 2044

def finiteProduct (a b : Value) : Prop :=
  -overflowUnits * oneUnits < units a * units b ∧
    units a * units b < overflowUnits * oneUnits

instance (a b : Value) : Decidable (finiteProduct a b) := inferInstanceAs (Decidable (_ ∧ _))

noncomputable def multiply? (a b : Value) : Option Value :=
  if finiteProduct a b then some (roundedMul a b) else none

def Multiplies (a b result : Value) : Prop := finiteProduct a b ∧ ProductRoundsNearestEven a b result

/-- The guarded operation accepts exactly the finite, nearest-even product
relation, including its zero sign. This characterizes every successful result. -/
theorem multiply_correct (a b result : Value) : multiply? a b = some result ↔ Multiplies a b result := by
  by_cases hd : finiteProduct a b
  · simp only [multiply?, Option.some.injEq, Multiplies, hd, if_true, true_and]
    exact ⟨fun h => h ▸ roundedMul_spec a b, fun h => product_rounding_unique (roundedMul_spec a b) h⟩
  · simp [multiply?, Multiplies, hd]

theorem multiply_complete (a b : Value) (h : finiteProduct a b) :
    ∃ result, multiply? a b = some result :=
  ⟨roundedMul a b, (multiply_correct _ _ _).mpr ⟨h, roundedMul_spec a b⟩⟩

theorem roundedMul_zero (a b : Value) (h : units a * units b = 0) :
    roundedMul a b = signedZero (negative a ^^ negative b) := by
  have hz : units positiveZero = 0 := by decide +kernel
  simp [roundedMul, h, Scaled.round_zero, hz]

private theorem product_scale (a b : Value) :
    ((units a * units b : Int) : ℝ) / (oneUnits * oneUnits) = value a * value b := by
  simp only [Int.cast_mul, value, div_mul_div_comm]

/-- The integer guard is exactly the open nearest-rounding interval around
zero in Real units. Crossing either threshold is rejected, not saturated. -/
theorem finiteProduct_real (a b : Value) : finiteProduct a b ↔
    -(overflowUnits : ℝ) / oneUnits < value a * value b ∧
      value a * value b < (overflowUnits : ℝ) / oneUnits := by
  have hp := oneUnits_real_pos
  have hl : (-(overflowUnits : ℝ) / oneUnits) * (oneUnits * oneUnits) =
      -(overflowUnits : ℝ) * oneUnits := by
    rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hp)]
  have hh : ((overflowUnits : ℝ) / oneUnits) * (oneUnits * oneUnits) =
      (overflowUnits : ℝ) * oneUnits := by
    rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hp)]
  rw [← product_scale, lt_div_iff₀ (mul_pos hp hp), div_lt_iff₀ (mul_pos hp hp), hl, hh]
  unfold finiteProduct
  constructor <;> intro h <;> constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2
  · exact_mod_cast h.1
  · exact_mod_cast h.2

theorem finiteProduct_zero (a b : Value) (h : units a * units b = 0) : finiteProduct a b := by
  have ht : (0 : Int) < overflowUnits := by decide +kernel
  have hp : (0 : Int) < oneUnits := by exact_mod_cast oneUnits_pos
  have hb := mul_pos ht hp
  simpa only [finiteProduct, h, neg_mul] using And.intro (neg_lt_zero.mpr hb) hb

theorem multiply_zero (a b : Value) (h : units a * units b = 0) :
    multiply? a b = some (signedZero (negative a ^^ negative b)) := by
  simp only [multiply?, if_pos (finiteProduct_zero a b h), roundedMul_zero a b h]

/-- Strict underflow is accepted and returns the signed zero, including
negative nonzero exact products. The nearest/even relation also covers ties. -/
theorem multiply_underflow (a b : Value) (small : 2 * (units a * units b).natAbs < oneUnits) :
    multiply? a b = some (signedZero (negative a ^^ negative b)) := by
  have hs : ((units a * units b).natAbs : Int) < oneUnits := by
    exact_mod_cast (show (units a * units b).natAbs < oneUnits by omega)
  have upper : units a * units b ≤ ((units a * units b).natAbs : Int) := Int.le_natAbs
  have lower : -((units a * units b).natAbs : Int) ≤ units a * units b := by
    have h : -(units a * units b) ≤ ((-(units a * units b)).natAbs : Int) := Int.le_natAbs
    simp only [Int.natAbs_neg] at h
    omega
  have hp : (0 : Int) ≤ oneUnits := Int.natCast_nonneg _
  have ht : (1 : Int) ≤ overflowUnits := by decide +kernel
  have bound : (oneUnits : Int) ≤ overflowUnits * oneUnits := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht hp
  have domain : finiteProduct a b := by
    simp only [finiteProduct, neg_mul]
    constructor <;> omega
  have hz : units positiveZero = 0 := by decide +kernel
  simp [multiply?, domain, roundedMul, Scaled.round_underflow small, hz]

theorem roundedMul_nearest (a b candidate : Value) :
    |value (roundedMul a b) - value a * value b| ≤ |value candidate - value a * value b| := by
  have h := Scaled.round_nearest oneUnits oneUnits_pos (units a * units b) candidate
  rw [product_scale, ← roundedMul_canonical, value_canonicalZero] at h
  exact h

theorem roundedMul_exact (a b candidate : Value) (h : value candidate = value a * value b) :
    value (roundedMul a b) = value a * value b := by
  have he := roundedMul_nearest a b candidate
  rw [h, sub_self, abs_zero] at he
  exact sub_eq_zero.mp (abs_nonpos_iff.mp he)

/-- Any representable bracket bounds error by half its width. Adjacent
binary64 values give the usual half-ulp bound, including the subnormal range. -/
theorem roundedMul_half_spacing (a b lo hi : Value)
    (hl : value lo ≤ value a * value b) (hh : value a * value b ≤ value hi) :
    |value (roundedMul a b) - value a * value b| ≤ (value hi - value lo) / 2 := by
  have ha := roundedMul_nearest a b lo
  have hb := roundedMul_nearest a b hi
  rw [abs_of_nonpos (show value lo - value a * value b ≤ 0 by linarith)] at ha
  rw [abs_of_nonneg (show 0 ≤ value hi - value a * value b by linarith)] at hb
  linarith

end Rumoca.Binary64
