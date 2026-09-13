import RumocaCore.Real.IntegerConversion

/-! Computed floor for finite binary64 encodings, connected to the
mathematical floor without native floating-point assumptions. -/
set_option exponentiation.threshold 2048
namespace Rumoca.Binary64

theorem small_exponent_units_bounds (x : Value) (small : exponent x < 1075) :
    -(2 ^ 1126 : Int) < units x ∧ units x < (2 ^ 1126 : Int) := by
  have fractionBound := fraction_bound x
  have mantissa : (if exponent x = 0 then fraction x else fractionCount + fraction x) < 2 ^ 53 := by
    split <;> simp only [fractionCount] at * <;> omega
  have power : 2 ^ (exponent x - 1) ≤ (2 : Nat) ^ 1073 :=
    Nat.pow_le_pow_right (by decide +kernel) (by omega)
  have magnitude : magnitudeUnits x < (2 : Nat) ^ 1126 := by
    unfold magnitudeUnits
    calc
      _ < 2 ^ 53 * 2 ^ (exponent x - 1) :=
        Nat.mul_lt_mul_of_pos_right mantissa (Nat.pow_pos (by decide +kernel))
      _ ≤ 2 ^ 53 * 2 ^ 1073 := Nat.mul_le_mul_left _ power
      _ = 2 ^ 1126 := by rw [← Nat.pow_add]
  have cast : (magnitudeUnits x : Int) < (2 : Int) ^ 1126 := by exact_mod_cast magnitude
  have positive : (0 : Int) < 2 ^ 1126 := by positivity
  unfold units
  split <;> omega

theorem small_exponent_value_bounds (x : Value) (small : exponent x < 1075) :
    -(2 ^ 52 : ℝ) < value x ∧ value x < (2 ^ 52 : ℝ) := by
  have bounds := small_exponent_units_bounds x small
  have lower : -(2 ^ 1126 : ℝ) < (units x : ℝ) := by exact_mod_cast bounds.1
  have upper : (units x : ℝ) < (2 ^ 1126 : ℝ) := by exact_mod_cast bounds.2
  have scale : (2 ^ 52 : ℝ) * (oneUnits : ℝ) = 2 ^ 1126 := by
    simp only [oneUnits, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
  constructor
  · rw [value, lt_div_iff₀ oneUnits_real_pos, neg_mul, scale]
    exact lower
  · rw [value, div_lt_iff₀ oneUnits_real_pos, scale]
    exact upper

theorem small_floor_fits (x : Value) (small : exponent x < 1075) :
    (floorInteger x).natAbs < 2 ^ 53 := by
  have bounds := small_exponent_value_bounds x small
  have lower : -(2 ^ 52 : Int) ≤ floorInteger x := by
    rw [floorInteger_eq, Int.le_floor]
    exact_mod_cast bounds.1.le
  have upper : floorInteger x < (2 ^ 52 : Int) := by
    rw [floorInteger_eq, Int.floor_lt]
    exact_mod_cast bounds.2
  have bigger : (2 ^ 52 : Int) < 2 ^ 53 := by decide +kernel
  omega

theorem large_exponent_integral (x : Value) (large : 1075 ≤ exponent x) :
    value x = (floorInteger x : ℝ) := by
  have power : oneUnits ∣ 2 ^ (exponent x - 1) :=
    Nat.pow_dvd_pow 2 (by omega)
  have magnitude : oneUnits ∣ magnitudeUnits x := dvd_mul_of_dvd_right power _
  have cast : (oneUnits : Int) ∣ (magnitudeUnits x : Int) := by exact_mod_cast magnitude
  have divisible : (oneUnits : Int) ∣ units x := by
    unfold units
    split
    · exact dvd_neg.mpr cast
    · exact cast
  have scaled : floorInteger x * (oneUnits : Int) = units x := Int.ediv_mul_cancel divisible
  symm
  apply (eq_div_iff oneUnits_real_pos.ne').mpr
  exact_mod_cast scaled

/-- Floor every finite binary64 value, preserving negative zero. Large
exponents already represent integers; smaller results use the proved encoder. -/
def floorValue (x : Value) : Value :=
  if x = negativeZero then negativeZero
  else if small : exponent x < 1075 then ofSmallInt (floorInteger x) (small_floor_fits x small)
  else x

theorem floorValue_correct (x : Value) : value (floorValue x) = (⌊value x⌋ : ℝ) := by
  unfold floorValue
  split
  · subst x
    have zero : value negativeZero = 0 := by simp [value, show units negativeZero = 0 by rfl]
    simp [zero]
  · split
    · rw [ofSmallInt_value, floorInteger_eq]
    · exact (large_exponent_integral x (by omega)).trans (by rw [floorInteger_eq])

theorem floorValue_negative_zero : floorValue negativeZero = negativeZero := by simp [floorValue]

theorem floorValue_bounds (x : Value) :
    value (floorValue x) ≤ value x ∧ value x < value (floorValue x) + 1 := by
  rw [floorValue_correct]
  exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

theorem floorValue_fixed_iff (x : Value) :
    value (floorValue x) = value x ↔ ∃ n : Int, value x = (n : ℝ) := by
  rw [floorValue_correct]
  constructor
  · intro same
    exact ⟨⌊value x⌋, same.symm⟩
  · rintro ⟨n, same⟩
    simp [same]

end Rumoca.Binary64
