import RumocaCore.Real.Encoding
import Mathlib.Data.Real.Archimedean

namespace Rumoca.Binary64

theorem normalCode_lt (biased fraction : Nat)
    (bounded : biased < 2047) (fractionBound : fraction < fractionCount) :
    biased * fractionCount + fraction < magnitudeCount := by
  have upper := Nat.add_lt_add_left fractionBound (biased * fractionCount)
  have exponentBound : (biased + 1) * fractionCount ≤ 2047 * fractionCount :=
    Nat.mul_le_mul_right fractionCount (by omega)
  unfold magnitudeCount
  nlinarith

/-- A normal positive encoding, with its actual biased exponent and fraction.
No rounding choice or native floating operation enters this construction. -/
def positiveNormal (biased fraction : Nat)
    (_normal : 0 < biased) (bounded : biased < 2047) (fractionBound : fraction < fractionCount) : Value :=
  ⟨biased * fractionCount + fraction,
    lt_of_lt_of_le (normalCode_lt biased fraction bounded fractionBound) (by unfold count; omega)⟩

theorem positiveNormal_fields (biased fraction : Nat)
    (normal : 0 < biased) (bounded : biased < 2047) (fractionBound : fraction < fractionCount) :
    let x := positiveNormal biased fraction normal bounded fractionBound
    negative x = false ∧ exponent x = biased ∧ Binary64.fraction x = fraction := by
  have codeBound := normalCode_lt biased fraction bounded fractionBound
  have positive : 0 < fractionCount := by decide +kernel
  have magnitude : magnitudeCode (positiveNormal biased fraction normal bounded fractionBound) =
      biased * fractionCount + fraction := Nat.mod_eq_of_lt codeBound
  refine ⟨by simp [negative, positiveNormal, Nat.not_le.mpr codeBound], ?_, ?_⟩
  · rw [exponent, magnitude, Nat.div_eq_iff positive]
    omega
  · simp [Binary64.fraction, magnitude, Nat.add_mod, Nat.mod_eq_of_lt fractionBound]

theorem positiveNormal_units (biased fraction : Nat)
    (normal : 0 < biased) (bounded : biased < 2047) (fractionBound : fraction < fractionCount) :
    units (positiveNormal biased fraction normal bounded fractionBound) =
      ((fractionCount + fraction) * 2 ^ (biased - 1) : Nat) := by
  obtain ⟨sign, exp, frac⟩ := positiveNormal_fields biased fraction normal bounded fractionBound
  simp [units, sign, magnitudeUnits, exp, frac, Nat.ne_of_gt normal]

/-- Shift a small positive integer into the 53-bit significand interval.
The exponent is obtained by the standard library's integer log2 algorithm. -/
theorem smallInteger_mantissa (n : Nat) (positive : 0 < n) (small : n < 2 ^ 53) :
    n.log2 ≤ 52 ∧ fractionCount ≤ n * 2 ^ (52 - n.log2) ∧
      n * 2 ^ (52 - n.log2) < 2 * fractionCount := by
  have nonzero : n ≠ 0 := Nat.ne_of_gt positive
  have exp := (Nat.log2_lt nonzero).mpr small
  have lower := Nat.log2_self_le nonzero
  have upper := Nat.lt_log2_self (n := n)
  have factor : 0 < 2 ^ (52 - n.log2) := Nat.pow_pos (by decide +kernel)
  have power : 2 ^ n.log2 * 2 ^ (52 - n.log2) = (2 : Nat) ^ 52 := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
  have nextPower : 2 ^ (n.log2 + 1) * 2 ^ (52 - n.log2) = (2 : Nat) ^ 53 := by
    rw [← Nat.pow_add, show n.log2 + 1 + (52 - n.log2) = 53 by omega]
  refine ⟨by omega, ?_, ?_⟩
  · simpa only [power, fractionCount] using Nat.mul_le_mul_right (2 ^ (52 - n.log2)) lower
  · have multiplied := Nat.mul_lt_mul_of_pos_right upper factor
    rw [nextPower] at multiplied
    simpa only [fractionCount, show (2 : Nat) ^ 53 = 2 * 2 ^ 52 by decide +kernel] using multiplied

/-- Exact conversion for every nonnegative integer below 2^53. Later C
admission can use this uniform bound instead of enumerating constants. -/
def ofSmallNat (n : Nat) (small : n < 2 ^ 53) : Value :=
  if positive : 0 < n then
    let bounds := smallInteger_mantissa n positive small
    positiveNormal (n.log2 + 1023) (n * 2 ^ (52 - n.log2) - fractionCount)
      (by omega) (by omega) (by omega)
  else positiveZero

set_option exponentiation.threshold 2048 in
theorem ofSmallNat_units (n : Nat) (small : n < 2 ^ 53) :
    units (ofSmallNat n small) = (n * oneUnits : Nat) := by
  by_cases positive : 0 < n
  · have bounds := smallInteger_mantissa n positive small
    unfold ofSmallNat
    rw [dif_pos positive, positiveNormal_units, Nat.add_sub_of_le bounds.2.1,
      Nat.mul_assoc, ← Nat.pow_add, show 52 - n.log2 + (n.log2 + 1023 - 1) = 1074 by omega]
    rfl
  · have zero : n = 0 := by omega
    subst n
    change units positiveZero = ((0 * oneUnits : Nat) : Int)
    rw [Nat.zero_mul]
    rfl

theorem ofSmallNat_value (n : Nat) (small : n < 2 ^ 53) :
    value (ofSmallNat n small) = (n : ℝ) := by
  simp [value, ofSmallNat_units, oneUnits_real_pos.ne']

/-- Flip only the sign of a finite encoding, including signed zero. -/
def negate (x : Value) : Value :=
  if low : x.val < magnitudeCount then
    ⟨x.val + magnitudeCount, by have bound := x.isLt; unfold count at *; omega⟩
  else
    ⟨x.val - magnitudeCount, by have bound := x.isLt; unfold count at *; omega⟩

theorem negate_fields (x : Value) :
    magnitudeCode (negate x) = magnitudeCode x ∧ negative (negate x) = !negative x := by
  have bound := x.isLt
  have positive : 0 < magnitudeCount := by decide +kernel
  unfold count at bound
  by_cases low : x.val < magnitudeCount
  · constructor
    · simp [magnitudeCode, negate, low]
    · simp [negative, negate, low, Nat.not_le.mpr low]
  · constructor
    · simp only [magnitudeCode, negate, dif_neg low]
      exact (Nat.mod_eq_sub_mod (Nat.le_of_not_lt low)).symm
    · have before : magnitudeCount ≤ x.val := by omega
      have after : x.val - magnitudeCount < magnitudeCount := by omega
      simp [negative, negate, low, before, Nat.not_le.mpr after]

theorem negate_units (x : Value) : units (negate x) = -units x := by
  obtain ⟨code, sign⟩ := negate_fields x
  have magnitude : magnitudeUnits (negate x) = magnitudeUnits x := by
    simp only [magnitudeUnits, exponent, fraction, code]
  simp only [units, sign, magnitude]
  cases negative x <;> simp

theorem negate_value (x : Value) : value (negate x) = -value x := by
  simp [value, negate_units, neg_div]

/-- Exact signed conversion throughout the 53-bit integer magnitude range. -/
def ofSmallInt (n : Int) (small : n.natAbs < 2 ^ 53) : Value :=
  match n with
  | .ofNat n => ofSmallNat n small
  | .negSucc n => negate (ofSmallNat (n + 1) small)

theorem ofSmallInt_value (n : Int) (small : n.natAbs < 2 ^ 53) :
    value (ofSmallInt n small) = (n : ℝ) := by
  cases n <;> simp [ofSmallInt, negate_value, ofSmallNat_value, Int.cast_negSucc]

def exactInteger? (n : Int) : Option Value :=
  if small : n.natAbs < 2 ^ 53 then some (ofSmallInt n small) else none

theorem exactInteger_sound (accepted : exactInteger? n = some result) : value result = (n : ℝ) := by
  unfold exactInteger? at accepted
  split at accepted
  · cases Option.some.inj accepted
    exact ofSmallInt_value _ _
  · contradiction

theorem exactInteger_complete (n : Int) (small : n.natAbs < 2 ^ 53) :
    ∃ result, exactInteger? n = some result ∧ value result = (n : ℝ) :=
  ⟨ofSmallInt n small, by simp only [exactInteger?, dif_pos small], ofSmallInt_value n small⟩

@[simp] theorem exactInteger_zero : exactInteger? 0 = some positiveZero := by rfl
@[simp] theorem exactInteger_one : exactInteger? 1 = some one := by rfl

def floorInteger (x : Value) : Int := units x / (oneUnits : Int)
def truncateInteger (x : Value) : Int := (units x).tdiv (oneUnits : Int)

theorem floorInteger_eq (x : Value) : floorInteger x = ⌊value x⌋ := by
  simp [floorInteger, value, Int.floor_div_natCast]

theorem truncateInteger_nonneg (x : Value) (nonnegative : 0 ≤ value x) :
    truncateInteger x = ⌊value x⌋ := by
  have numeratorReal : (0 : ℝ) ≤ (units x : ℝ) := by
    simpa only [zero_mul] using (le_div_iff₀ oneUnits_real_pos).mp nonnegative
  have numerator : 0 ≤ units x := by exact_mod_cast numeratorReal
  rw [truncateInteger, Int.tdiv_eq_ediv_of_nonneg numerator]
  exact floorInteger_eq x

theorem truncateInteger_nonpos (x : Value) (nonpositive : value x ≤ 0) :
    truncateInteger x = ⌈value x⌉ := by
  have opposite := truncateInteger_nonneg (negate x) (by rw [negate_value]; linarith)
  simp only [truncateInteger, negate_units, Int.neg_tdiv, negate_value, Int.floor_neg] at opposite
  exact neg_injective opposite

/-- C's finite floating-to-integer rule, expressed independently using
mathlib's mathematical floor/ceiling, is implemented by integer-unit tdiv. -/
theorem truncateInteger_correct (x : Value) :
    truncateInteger x = if 0 ≤ value x then ⌊value x⌋ else ⌈value x⌉ := by
  split
  · exact truncateInteger_nonneg x ‹_›
  · exact truncateInteger_nonpos x (le_of_not_ge ‹_›)

theorem truncateInteger_exact (x : Value) (n : Int) (exactValue : value x = (n : ℝ)) :
    truncateInteger x = n := by
  rw [truncateInteger_correct, exactValue]
  split <;> simp

theorem truncateInteger_bounded (x : Value) (maximum : Nat)
    (nonnegative : 0 ≤ value x) (bounded : value x ≤ (maximum : ℝ)) :
    0 ≤ truncateInteger x ∧ truncateInteger x ≤ (maximum : Int) := by
  rw [truncateInteger_nonneg x nonnegative]
  constructor
  · exact Int.floor_nonneg.mpr nonnegative
  · simpa using Int.floor_mono bounded

theorem exactInteger_truncate (accepted : exactInteger? n = some result) :
    truncateInteger result = n :=
  truncateInteger_exact result n (exactInteger_sound accepted)

/-- A bounded nonnegative library-floor call has an explicit representable
result, computed from units and the integer encoder. This is a mathematical
result for later call contracts, not an assumption that the call succeeds. -/
theorem bounded_floor_representable (x : Value) (maximum : Nat) (small : maximum < 2 ^ 53)
    (nonnegative : 0 ≤ value x) (bounded : value x ≤ (maximum : ℝ)) :
    ∃ result, exactInteger? (floorInteger x) = some result ∧
      value result = (⌊value x⌋ : ℝ) := by
  have bounds : 0 ≤ floorInteger x ∧ floorInteger x ≤ (maximum : Int) := by
    rw [floorInteger_eq, ← truncateInteger_nonneg x nonnegative]
    exact truncateInteger_bounded x maximum nonnegative bounded
  have fits : (floorInteger x).natAbs < 2 ^ 53 := by
    have cast : ((floorInteger x).natAbs : Int) < ((2 ^ 53 : Nat) : Int) := by
      rw [Int.natAbs_of_nonneg bounds.1]
      exact lt_of_le_of_lt bounds.2 (by exact_mod_cast small)
    exact_mod_cast cast
  obtain ⟨result, accepted, represented⟩ := exactInteger_complete (floorInteger x) fits
  exact ⟨result, accepted, by simpa only [floorInteger_eq] using represented⟩

end Rumoca.Binary64
