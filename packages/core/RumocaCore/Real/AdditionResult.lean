import RumocaCore.Real.Addition
import RumocaCore.Real.Multiplication
import RumocaCore.Real.Comparison

/-! Nearest-even addition of arbitrary finite operands, including overflow.
The numerical relation covers result bits; exception flags and traps remain
outside this authored semantics and require separate correspondence. -/

set_option maxRecDepth 10000
set_option exponentiation.threshold 4096

namespace Rumoca.Float64
open Binary64

/-- One canonical NaN is enough for the decoded numerical domain. Arbitrary
input payloads still use `decode`; this is not a payload-preserving inverse. -/
def Number.encode : Number → BitVec 64
  | .finite x => (toBits x).val
  | .negativeInfinity => BitVec.ofNat 64 (signPlace + magnitudeCount)
  | .positiveInfinity => BitVec.ofNat 64 magnitudeCount
  | .nan => BitVec.ofNat 64 (magnitudeCount + 1)

@[simp] theorem decode_encode (x : Number) : decode x.encode = x := by
  cases x with
  | finite x => exact decode_finite x
  | negativeInfinity => decide +kernel
  | positiveInfinity => decide +kernel
  | nan => decide +kernel

theorem encode_injective : Function.Injective Number.encode :=
  Function.LeftInverse.injective decode_encode

end Rumoca.Float64

namespace Rumoca.Binary64
open Rumoca.Float64
noncomputable section

/-- Signed-zero-aware addition rounding. The ordinary nearest/even relation
fixes every other result independently of the chosen rounding implementation. -/
def SumRoundsNearestEven (a b result : Value) : Prop :=
  if a = negativeZero ∧ b = negativeZero then result = negativeZero
  else RoundsNearestEven (units a + units b) result

theorem roundedAdd_spec (a b : Value) : SumRoundsNearestEven a b (roundedAdd a b) := by
  unfold SumRoundsNearestEven roundedAdd
  split
  · rfl
  · exact round_spec _

theorem sum_rounding_unique (first : SumRoundsNearestEven a b x)
    (second : SumRoundsNearestEven a b y) : x = y := by
  by_cases zero : a = negativeZero ∧ b = negativeZero
  · rw [SumRoundsNearestEven, if_pos zero] at first second
    exact first.trans second.symm
  · rw [SumRoundsNearestEven, if_neg zero] at first second
    exact rounding_unique first second

/-- Nearest-even overflow threshold in mathematical units. Exception flags
and trapping environments are outside this numerical result relation. -/
def overflowValue : ℝ := (overflowUnits : ℝ) / oneUnits

theorem overflowValue_pos : 0 < overflowValue := by
  have positive : (0 : Int) < overflowUnits := by decide +kernel
  exact div_pos (by exact_mod_cast positive) oneUnits_real_pos

theorem sum_below_overflow (a b : Value) :
    value a + value b < overflowValue ↔ units a + units b < overflowUnits := by
  unfold value overflowValue
  rw [← add_div, div_lt_div_iff_of_pos_right oneUnits_real_pos]
  exact_mod_cast Iff.rfl

theorem sum_above_negative_overflow (a b : Value) :
    -overflowValue < value a + value b ↔ -overflowUnits < units a + units b := by
  unfold value overflowValue
  rw [← neg_div, ← add_div, div_lt_div_iff_of_pos_right oneUnits_real_pos]
  exact_mod_cast Iff.rfl

/-- Independent result relation for any pair of finite operands. Threshold
ties overflow in nearest-even mode; the finite branch retains exact sign and
rounding constraints. A finite-input addition never produces NaN. -/
def Adds (a b : Value) : Number → Prop
  | .negativeInfinity => value a + value b ≤ -overflowValue
  | .positiveInfinity => overflowValue ≤ value a + value b
  | .finite result => -overflowValue < value a + value b ∧
      value a + value b < overflowValue ∧ SumRoundsNearestEven a b result
  | .nan => False

/-- Total numerical addition of finite operands under nearest-even rounding.
This semantic function is not executed by the production compiler. -/
def addResult (a b : Value) : Number :=
  if units a + units b ≤ -overflowUnits then .negativeInfinity
  else if overflowUnits ≤ units a + units b then .positiveInfinity
  else .finite (roundedAdd a b)

theorem addResult_spec (a b : Value) : Adds a b (addResult a b) := by
  unfold addResult
  split
  · change value a + value b ≤ -overflowValue
    exact le_of_not_gt (fun h => not_lt_of_ge ‹_› ((sum_above_negative_overflow a b).mp h))
  · split
    · change overflowValue ≤ value a + value b
      exact le_of_not_gt (fun h => not_lt_of_ge ‹_› ((sum_below_overflow a b).mp h))
    · exact ⟨(sum_above_negative_overflow a b).mpr (lt_of_not_ge ‹_›),
        (sum_below_overflow a b).mpr (lt_of_not_ge ‹_›), roundedAdd_spec a b⟩

theorem adds_unique (first : Adds a b x) (second : Adds a b y) : x = y := by
  have positive := overflowValue_pos
  cases x <;> cases y <;> simp only [Adds] at first second
  all_goals try rfl
  case finite.finite x y => exact congrArg Number.finite (sum_rounding_unique first.2.2 second.2.2)
  all_goals
    try obtain ⟨lower, upper, _⟩ := first
    try obtain ⟨lower', upper', _⟩ := second
    exfalso
    linarith

theorem addResult_correct (a b : Value) (result : Number) :
    addResult a b = result ↔ Adds a b result :=
  ⟨fun same => same ▸ addResult_spec a b, fun spec => adds_unique (addResult_spec a b) spec⟩

theorem addResult_finite (a b : Value)
    (bounded : -overflowUnits < units a + units b ∧ units a + units b < overflowUnits) :
    addResult a b = .finite (roundedAdd a b) := by
  simp only [addResult, if_neg (not_le_of_gt bounded.1), if_neg (not_le_of_gt bounded.2)]

theorem addResult_no_nan (a b : Value) : addResult a b ≠ .nan := by
  intro same
  exact (addResult_correct a b .nan).mp same

end
end Rumoca.Binary64
