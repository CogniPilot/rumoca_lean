import RumocaCore.Real.Encoding

/-! Ordered and unordered comparisons on IEEE binary64 encodings. Finite
operands reuse the proved encoding bijection and exact integer-unit decoding.
Both infinities and every NaN payload are classified. This models comparison
results, not floating exception flags, signaling traps or the host fenv. -/
namespace Rumoca.Float64
open Binary64
set_option maxRecDepth 10000

inductive Number where
  | finite (value : Binary64.Value)
  | negativeInfinity
  | positiveInfinity
  | nan
  deriving DecidableEq

def decode (bits : BitVec 64) : Number :=
  if h : bits.toNat % signPlace < magnitudeCount then .finite (ofBits ⟨bits, h⟩)
  else if bits.toNat % signPlace = magnitudeCount then
    if bits.toNat < signPlace then .positiveInfinity else .negativeInfinity
  else .nan

@[simp] theorem decode_finite (x : Binary64.Value) :
    decode (toBits x).val = .finite x := by
  simp [decode, (toBits x).property, ofBits_toBits]

theorem decode_nan (bits : BitVec 64) (h : magnitudeCount < bits.toNat % signPlace) :
    decode bits = .nan := by
  simp [decode, Nat.not_lt_of_ge (Nat.le_of_lt h), Nat.ne_of_gt h]

/-- `none` is unordered, not a failure to decode the bit pattern. -/
def Number.compare : Number → Number → Option Ordering
  | .nan, _ | _, .nan => none
  | .finite a, .finite b => some (Ord.compare (units a) (units b))
  | .negativeInfinity, .negativeInfinity | .positiveInfinity, .positiveInfinity => some .eq
  | .negativeInfinity, _ | _, .positiveInfinity => some .lt
  | .positiveInfinity, _ | _, .negativeInfinity => some .gt

def compareBits (a b : BitVec 64) : Option Ordering := (decode a).compare (decode b)

inductive Relation where | eq | ne | lt | le | gt | ge
  deriving DecidableEq

def test (relation : Relation) (a b : BitVec 64) : Bool :=
  let order := compareBits a b
  match relation with
  | .eq => decide (order = some .eq)
  | .ne => decide (order ≠ some .eq)
  | .lt => decide (order = some .lt)
  | .le => decide (order = some .lt ∨ order = some .eq)
  | .gt => decide (order = some .gt)
  | .ge => decide (order = some .gt ∨ order = some .eq)

/-- Mathematical reference for finite operands. Floating encoding equality
is deliberately absent: +0 and -0 have the same numerical value. -/
def Relation.Holds (relation : Relation) (a b : ℝ) : Prop :=
  match relation with
  | .eq => a = b | .ne => a ≠ b
  | .lt => a < b | .le => a ≤ b
  | .gt => b < a | .ge => b ≤ a

theorem value_eq_iff (a b : Binary64.Value) : value a = value b ↔ units a = units b := by
  simp [value, div_left_inj' (ne_of_gt oneUnits_real_pos)]

theorem value_lt_iff (a b : Binary64.Value) : value a < value b ↔ units a < units b := by
  simp [value, div_lt_div_iff_of_pos_right oneUnits_real_pos]

theorem value_le_iff (a b : Binary64.Value) : value a ≤ value b ↔ units a ≤ units b := by
  simp [value, div_le_div_iff_of_pos_right oneUnits_real_pos]

theorem test_finite (relation : Relation) (a b : Binary64.Value) :
    test relation (toBits a).val (toBits b).val = true ↔
      relation.Holds (value a) (value b) := by
  cases relation <;>
    simp only [test, compareBits, decode_finite, Number.compare, Relation.Holds,
      decide_eq_true_eq, Option.some.injEq, ne_eq,
      compare_eq_iff_eq, compare_lt_iff_lt, compare_gt_iff_gt,
      value_eq_iff, value_lt_iff, le_iff_lt_or_eq]
  exact or_congr_right eq_comm

theorem test_finite_false (relation : Relation) (a b : Binary64.Value) :
    test relation (toBits a).val (toBits b).val = false ↔
      ¬ relation.Holds (value a) (value b) := by
  simp only [Bool.eq_false_iff, ne_eq, test_finite]

theorem unordered_left (ha : decode a = .nan) (b) :
    test .eq a b = false ∧ test .ne a b = true ∧
    test .lt a b = false ∧ test .le a b = false ∧
    test .gt a b = false ∧ test .ge a b = false := by
  simp [test, compareBits, ha, Number.compare]

theorem unordered_right (hb : decode b = .nan) (a) :
    test .eq a b = false ∧ test .ne a b = true ∧
    test .lt a b = false ∧ test .le a b = false ∧
    test .gt a b = false ∧ test .ge a b = false := by
  cases ha : decode a <;> simp [test, compareBits, ha, hb, Number.compare]

end Rumoca.Float64
