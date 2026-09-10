import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Finite IEEE754 binary64 values and their round-to-nearest-even semantics.
Values are decoded exactly in units of 2^-1074. The specification's finite
minimization is mathematical, never executed or linked into the compiler.
No property of Lean's opaque native Float operations is assumed. -/
namespace Rumoca.Binary64

set_option maxRecDepth 10000
set_option exponentiation.threshold 4096

def fractionCount : Nat := 2 ^ 52
def magnitudeCount : Nat := 2047 * fractionCount
def count : Nat := 2 * magnitudeCount

/-- All finite encodings, including both signed zeros. Exponent 2047 (NaN/Inf)
is excluded. Negative encodings follow the positive ones. -/
abbrev Value := Fin count

def negative (x : Value) : Bool := x.val ≥ magnitudeCount
def magnitudeCode (x : Value) : Nat := x.val % magnitudeCount
def exponent (x : Value) : Nat := magnitudeCode x / fractionCount
def fraction (x : Value) : Nat := magnitudeCode x % fractionCount

def magnitudeUnits (x : Value) : Nat :=
  (if exponent x = 0 then fraction x else fractionCount + fraction x) * 2 ^ (exponent x - 1)

def units (x : Value) : Int :=
  if negative x then -(magnitudeUnits x : Int) else magnitudeUnits x

def oneUnits : Nat := 2 ^ 1074
def maxUnits : Nat := (2 ^ 53 - 1) * 2 ^ 2045

noncomputable def value (x : Value) : ℝ := (units x : ℝ) / (oneUnits : ℝ)

def one : Value := ⟨1023 * fractionCount, by decide +kernel⟩
def positiveZero : Value := ⟨0, by decide +kernel⟩
def negativeZero : Value := ⟨magnitudeCount, by decide +kernel⟩

theorem units_one : units one = (oneUnits : Int) := by decide +kernel

theorem oneUnits_pos : 0 < oneUnits := Nat.pow_pos (by decide)
theorem oneUnits_real_pos : (0 : ℝ) < oneUnits := by exact_mod_cast oneUnits_pos

theorem value_one : value one = 1 := by
  simp only [value, units_one, Int.cast_natCast, div_self (ne_of_gt oneUnits_real_pos)]

theorem exponent_bound (x : Value) : exponent x ≤ 2046 := by
  have h := Nat.mod_lt x.val (by decide : 0 < magnitudeCount)
  simp only [exponent, magnitudeCode, magnitudeCount, fractionCount] at *
  omega

theorem fraction_bound (x : Value) : fraction x < fractionCount :=
  Nat.mod_lt _ (by decide)

theorem magnitude_bound (x : Value) : magnitudeUnits x ≤ maxUnits := by
  have he := exponent_bound x
  have hf := fraction_bound x
  have hc : (if exponent x = 0 then fraction x else fractionCount + fraction x) ≤ 2 ^ 53 - 1 := by
    split <;> simp only [fractionCount] at * <;> omega
  have hp : 2 ^ (exponent x - 1) ≤ 2 ^ 2045 := Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.mul_le_mul hc hp

theorem units_bound (x : Value) : -(maxUnits : Int) ≤ units x ∧ units x ≤ maxUnits := by
  have hm := magnitude_bound x
  unfold units
  split <;> omega

/-- Exact sum x+1 lies strictly below the IEEE nearest-rounding overflow
threshold on both sides, even for the largest finite binary64 input. -/
theorem advance_no_overflow (x : Value) :
    -(maxUnits + 2 ^ 2044 : Int) < units x + oneUnits ∧
    units x + oneUnits < (maxUnits + 2 ^ 2044 : Int) := by
  have h := units_bound x
  have hp : (oneUnits : Int) < 2 ^ 2044 := by decide +kernel
  have ho : (0 : Int) < oneUnits := by exact_mod_cast oneUnits_pos
  constructor <;> omega

/-- Fraction bit zero is also significand bit zero for normal numbers. -/
def parity (x : Value) : Nat := fraction x % 2

def distance (z : Int) (x : Value) : Nat := (units x - z).natAbs

/-- Lexicographic rank: exact distance, then even significand, then encoding.
The last tie-break chooses +0 over -0. -/
def cost (z : Int) (x : Value) : Nat := (distance z x * 2 + parity x) * count + x.val

theorem parity_bound (x : Value) : parity x < 2 := Nat.mod_lt _ (by decide)

private theorem minimum_exists (z : Int) : ∃ x : Value, ∀ y : Value, cost z x ≤ cost z y := by
  have hn : (Finset.univ : Finset Value).Nonempty := ⟨one, Finset.mem_univ _⟩
  obtain ⟨x, _, hx⟩ := Finset.exists_min_image Finset.univ (cost z) hn
  exact ⟨x, fun y => hx y (Finset.mem_univ y)⟩

/-- Kernel-checked witness with an opaque implementation. Keeping the witness
opaque prevents reduction from attempting to enumerate the binary64 universe
when a theorem specializes the rounding argument to a concrete integer. -/
noncomputable opaque roundWitness (z : Int) : { x : Value // ∀ y : Value, cost z x ≤ cost z y } :=
  ⟨Classical.choose (minimum_exists z), Classical.choose_spec (minimum_exists z)⟩

noncomputable def round (z : Int) : Value := (roundWitness z).val

theorem round_cost_le (z : Int) (y : Value) : cost z (round z) ≤ cost z y :=
  (roundWitness z).property y

theorem round_nearest (z : Int) (y : Value) : distance z (round z) ≤ distance z y := by
  have hc := round_cost_le z y
  have hp := parity_bound (round z)
  have hq := parity_bound y
  have hr := (round z).isLt
  have hy := y.isLt
  simp only [cost, count, magnitudeCount, fractionCount] at hc hr hy
  omega

theorem round_ties_even (z : Int) (y : Value)
    (hd : distance z (round z) = distance z y) (he : parity y = 0) : parity (round z) = 0 := by
  have hc := round_cost_le z y
  have hp := parity_bound (round z)
  have hr := (round z).isLt
  have hy := y.isLt
  simp only [cost, hd, he, count, magnitudeCount, fractionCount] at hc hr hy
  omega

/-- Declarative IEEE nearest/even rule for a finite result. Encodings break
the sole duplicated-value tie (+0 and -0) in favor of positive zero. -/
structure RoundsNearestEven (z : Int) (x : Value) : Prop where
  nearest : ∀ y, distance z x ≤ distance z y
  even : ∀ y, distance z x = distance z y → parity x ≤ parity y
  canonical : ∀ y, distance z x = distance z y → parity x = parity y → x.val ≤ y.val

theorem round_spec (z : Int) : RoundsNearestEven z (round z) := by
  refine ⟨round_nearest z, ?_, ?_⟩
  · intro y hd
    have hc := round_cost_le z y
    have hp := parity_bound (round z)
    have hq := parity_bound y
    have hr := (round z).isLt
    have hy := y.isLt
    simp only [cost, hd, count, magnitudeCount, fractionCount] at hc hr hy
    omega
  · intro y hd hp
    have hc := round_cost_le z y
    simp only [cost, hd, hp] at hc
    omega

theorem rounding_unique (ha : RoundsNearestEven z a) (hb : RoundsNearestEven z b) : a = b := by
  have hd := Nat.le_antisymm (ha.nearest b) (hb.nearest a)
  have hp := Nat.le_antisymm (ha.even b hd) (hb.even a hd.symm)
  exact Fin.ext (Nat.le_antisymm (ha.canonical b hd hp) (hb.canonical a hd.symm hp.symm))

theorem round_exact (x : Value) : units (round (units x)) = units x := by
  have h := round_nearest (units x) x
  simp only [distance, sub_self, Int.natAbs_zero, Nat.le_zero] at h
  exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp h)

private theorem round_eq_of_cost_zero (z : Int) (x : Value) (hz : cost z x = 0) : round z = x := by
  have h := round_cost_le z x
  rw [hz] at h
  have hx : x.val = 0 := by unfold cost at hz; omega
  have hr : (round z).val = 0 := by unfold cost at h; omega
  exact Fin.ext (hr.trans hx.symm)

theorem round_zero : round 0 = positiveZero :=
  round_eq_of_cost_zero 0 positiveZero (by decide +kernel)

noncomputable def advance (x : Value) : Value := round (units x + oneUnits)

/-- Nearest-even addition retains -0 when both operands are -0. Other exact
zero sums use +0 via the canonical rounding rule. Overflow is checked by the
expression evaluator before invoking this finite-result primitive. -/
noncomputable def roundedAdd (a b : Value) : Value :=
  if a = negativeZero ∧ b = negativeZero then negativeZero else round (units a + units b)

theorem roundedAdd_negative_zero : roundedAdd negativeZero negativeZero = negativeZero := by
  simp only [roundedAdd, and_self, if_true]

theorem roundedAdd_one (x : Value) : roundedAdd x one = advance x := by
  have hn : one ≠ negativeZero := by decide +kernel
  simp only [roundedAdd, hn, and_false, if_false, units_one, advance]

theorem roundedAdd_positive_zero : roundedAdd positiveZero positiveZero = positiveZero := by
  have hn : positiveZero ≠ negativeZero := by decide +kernel
  have hu : units positiveZero = 0 := by decide +kernel
  simp only [roundedAdd, hn, false_and, if_false, hu, add_zero, round_zero]

/-- A useful global bound specific to der(x)=1. It includes stagnation when
one is smaller than half an ulp, where a unit-step error of one is possible. -/
theorem advance_error_units (x : Value) :
    (units (advance x) - (units x + oneUnits)).natAbs ≤ oneUnits := by
  have h := round_nearest (units x + oneUnits) x
  change (units (advance x) - (units x + oneUnits)).natAbs ≤ (units x - (units x + oneUnits)).natAbs at h
  have he : units x - (units x + oneUnits) = -(oneUnits : Int) := by omega
  simpa only [he, Int.natAbs_neg, Int.natAbs_natCast] using h

end Rumoca.Binary64

namespace Rumoca.Binary64

set_option maxRecDepth 10000

private theorem error_scale (a : Value) (z : Int) :
    |value a - (z : ℝ) / oneUnits| = (distance z a : ℝ) / oneUnits := by
  rw [value, ← sub_div, abs_div, abs_of_pos oneUnits_real_pos]
  congr 1
  simp only [distance, Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]

theorem advance_nearest (x y : Value) :
    |value (advance x) - (value x + 1)| ≤ |value y - (value x + 1)| := by
  have hz : (((units x + oneUnits : Int) : ℝ) / oneUnits) = value x + 1 := by
    simp only [Int.cast_add, Int.cast_natCast, add_div, value, div_self (ne_of_gt oneUnits_real_pos)]
  rw [← hz, error_scale, error_scale]
  apply (div_le_div_iff_of_pos_right oneUnits_real_pos).mpr
  exact_mod_cast round_nearest (units x + oneUnits) y

theorem advance_error (x : Value) : |value (advance x) - (value x + 1)| ≤ 1 := by
  have h := advance_nearest x x
  have he : value x - (value x + 1) = (-1 : ℝ) := by ring
  simpa only [he, abs_neg, abs_one] using h

/-- If the exact sum is representable, rounding has zero error. -/
theorem advance_exact (x y : Value) (h : value y = value x + 1) :
    value (advance x) = value x + 1 := by
  have he := advance_nearest x y
  rw [h, sub_self, abs_zero] at he
  exact sub_eq_zero.mp (abs_nonpos_iff.mp he)

/-- For any representable bracket, the error is at most half its width.
An adjacent bracket gives the usual half-ulp bound. -/
theorem advance_half_spacing (x lo hi : Value)
    (hl : value lo ≤ value x + 1) (hh : value x + 1 ≤ value hi) :
    |value (advance x) - (value x + 1)| ≤ (value hi - value lo) / 2 := by
  have ha := advance_nearest x lo
  have hb := advance_nearest x hi
  rw [abs_of_nonpos (show value lo - (value x + 1) ≤ 0 by linarith)] at ha
  rw [abs_of_nonneg (show 0 ≤ value hi - (value x + 1) by linarith)] at hb
  linarith

noncomputable def run (x : Value) : Nat → Value
  | 0 => x
  | n + 1 => run (advance x) n

theorem run_succ (x : Value) (n : Nat) : run x (n + 1) = advance (run x n) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (advance x)

/-- An exactness regime, separate from the worst-case global error bound:
when all ideal samples through n are representable, every sample is exact. -/
theorem run_exact (x : Value) (n : Nat)
    (h : ∀ k ≤ n, ∃ y : Value, value y = value x + k) :
    value (run x n) = value x + n := by
  induction n with
  | zero => simp only [run, Nat.cast_zero, add_zero]
  | succ n ih =>
    have hi := ih (fun k hk => h k (by omega))
    obtain ⟨y, hy⟩ := h (n + 1) (by omega)
    rw [run_succ, advance_exact (run x n) y (by rw [hi]; simpa [Nat.cast_add, add_assoc] using hy), hi]
    simp only [Nat.cast_add, Nat.cast_one, add_assoc]

/-- All finite binary64 starts, including negative values and subnormals.
There is no overflow or magnitude precondition for this particular unit RHS. -/
theorem run_error (x : Value) (n : Nat) :
    |value (run x n) - (value x + n)| ≤ n := by
  induction n generalizing x with
  | zero => simp only [run, Nat.cast_zero, add_zero, sub_self, abs_zero, le_refl]
  | succ n ih =>
    have ht := ih (advance x)
    have hs := advance_error x
    have he : value (run (advance x) n) - (value x + (n + 1 : Nat)) =
        (value (run (advance x) n) - (value (advance x) + n)) +
        (value (advance x) - (value x + 1)) := by push_cast; ring
    simp only [run]
    rw [he]
    calc
      _ ≤ |value (run (advance x) n) - (value (advance x) + n)| +
          |value (advance x) - (value x + 1)| := abs_add_le _ _
      _ ≤ (n : ℝ) + 1 := add_le_add ht hs
      _ = _ := by push_cast; ring

/-- A concrete fractional-state example checked with exact encodings, without
executing or trusting the host's native Float implementation. -/
def half : Value := ⟨1022 * fractionCount, by decide +kernel⟩
def threeHalves : Value := ⟨1023 * fractionCount + fractionCount / 2, by decide +kernel⟩

theorem value_half : value half = 1 / 2 := by
  have hi : (2 : Int) * units half = oneUnits := by decide +kernel
  have hr : (2 : ℝ) * (units half : ℝ) = oneUnits := by exact_mod_cast hi
  apply (div_eq_iff (ne_of_gt oneUnits_real_pos)).mpr
  linarith

theorem value_threeHalves : value threeHalves = 3 / 2 := by
  have hi : (2 : Int) * units threeHalves = 3 * oneUnits := by decide +kernel
  have hr : (2 : ℝ) * (units threeHalves : ℝ) = 3 * oneUnits := by exact_mod_cast hi
  apply (div_eq_iff (ne_of_gt oneUnits_real_pos)).mpr
  linarith

theorem advance_half : value (advance half) = 3 / 2 := by
  have hr : value threeHalves = value half + 1 := by rw [value_half, value_threeHalves]; norm_num
  rw [advance_exact half threeHalves hr, value_half]
  norm_num

end Rumoca.Binary64
