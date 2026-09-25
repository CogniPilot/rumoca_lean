import RumocaC.Body
import RumocaCore.Real.IntegerConversion

/-! Values of the floating constants `Expr.real k`. The constant is the decimal
`ke0`; its binary64 value is the correctly rounded conversion of `k`
(`CBody.decimalValue`, the translator boundary of C11 6.4.4.2), which is exact for
every `k` below 2^53. Zero converts to `+0` and one to the encoding `one`, the
same values the integer constants `0` and `1` convert to on a floating store. -/
namespace Rumoca.CBody
open CTree Binary64

set_option exponentiation.threshold 2048

/-- Every finite encoding below the encoding of `1.0` denotes less than one. -/
theorem units_below_one (y : Binary64.Value) (below : y.val < one.val) : units y < (oneUnits : Int) := by
  have hv : y.val < 1023 * 2 ^ 52 := by simpa [one, fractionCount] using below
  have hneg : negative y = false := by
    simp only [negative, magnitudeCount, fractionCount, decide_eq_false_iff_not, not_le]; omega
  have hcode : magnitudeCode y = y.val :=
    Nat.mod_eq_of_lt (by simp only [magnitudeCount, fractionCount]; omega)
  have he : exponent y ≤ 1022 := by
    simp only [exponent, hcode, fractionCount]
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by positivity)).mpr (by omega))
  have hf := fraction_bound y
  have hs : (if exponent y = 0 then fraction y else fractionCount + fraction y) < 2 ^ 53 := by
    simp only [fractionCount] at hf ⊢; split <;> omega
  have hp : 2 ^ (exponent y - 1) ≤ 2 ^ 1021 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm : magnitudeUnits y < 2 ^ 1074 :=
    calc magnitudeUnits y < 2 ^ 53 * 2 ^ (exponent y - 1) :=
          Nat.mul_lt_mul_of_pos_right hs (Nat.pow_pos (by norm_num))
      _ ≤ 2 ^ 53 * 2 ^ 1021 := Nat.mul_le_mul_left _ hp
      _ = 2 ^ 1074 := by norm_num
  simp only [units, hneg, Bool.false_eq_true, ↓reduceIte, oneUnits]
  exact_mod_cast hm

/-- Rounding the exact units of one yields the encoding `one`. -/
theorem round_oneUnits : Binary64.round (oneUnits : Int) = one := by
  apply rounding_unique (round_spec _)
  have hd : distance (oneUnits : Int) one = 0 := by simp [distance, units_one]
  refine ⟨fun y => by rw [hd]; exact Nat.zero_le _, fun y _ => by
    simp [parity, fraction, magnitudeCode, one, fractionCount, magnitudeCount], fun y same _ => ?_⟩
  by_contra lt
  have hu := units_below_one y (by omega)
  rw [hd] at same
  have : units y = oneUnits := by
    have := same.symm; simp only [distance, Int.natAbs_eq_zero, sub_eq_zero] at this; exact this
  omega

/-- The constant `ke0` is the rounding of `k` whole units. -/
theorem decimal_integer (k : Nat) :
    decimalValue false k 0 = Binary64.round ((k * oneUnits : Nat) : Int) := by
  simp [decimalValue, decimalScale, decimalNumerator, Scaled.round_one]

@[simp] theorem decimal_zero : decimalValue false 0 0 = positiveZero := by
  simp [decimalValue, decimalScale, decimalNumerator, Scaled.round_zero]

@[simp] theorem decimal_one : decimalValue false 1 0 = one := by
  rw [decimal_integer, Nat.one_mul]; exact round_oneUnits

/-- The value of `+0` is zero. -/
theorem value_positiveZero : Binary64.value Binary64.positiveZero = 0 := by
  simp [Binary64.value, show Binary64.units Binary64.positiveZero = 0 by decide +kernel]

/-- Below 2^53 the constant `ke0` denotes exactly `k`. -/
theorem decimal_value (k : Nat) (small : k < 2 ^ 53) : value (decimalValue false k 0) = k := by
  have hu : units (decimalValue false k 0) = (k * oneUnits : Nat) := by
    rw [decimal_integer, ← ofSmallNat_units k small, round_exact]
  simp only [value, hu, Nat.cast_mul]; push_cast; field_simp [oneUnits_real_pos.ne']

variable [interface : CInterface]

/-- `Expr.real k` evaluates to the rounded value of `k`, independent of the
environment, the heap and the interface. -/
@[simp] theorem eval_real (env : Locals) (heap : CMemory.Heap) (k : Nat) :
    eval env heap (Expr.real k) = some (.finite (decimalValue false k 0)) := rfl

end Rumoca.CBody
