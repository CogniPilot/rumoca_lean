import RumocaCore.Real.MultiplicationResult
import RumocaCore.Real.Classification

/-! IEEE 754 binary64 addition and multiplication (round to nearest, ties to
even) on the complete numerical domain. Finite operands use the proved total
results `addResult`/`mulResult`; non-finite operands follow the IEEE special
cases: NaN propagates, opposite infinities sum to NaN, an infinity times a
zero is NaN, and otherwise an infinity absorbs the other operand, with the
product sign for multiplication. A non-finite operand therefore never yields
a finite result. This models numerical results, not exception flags, traps or
the host floating environment. -/
noncomputable section
namespace Rumoca.Float64
open Binary64

/-- The infinity with the given sign. -/
def Number.infinity (negative : Bool) : Number :=
  if negative then .negativeInfinity else .positiveInfinity

def Number.add : Number → Number → Number
  | .finite a, .finite b => addResult a b
  | .nan, _ => .nan
  | _, .nan => .nan
  | .positiveInfinity, .negativeInfinity => .nan
  | .negativeInfinity, .positiveInfinity => .nan
  | .positiveInfinity, _ => .positiveInfinity
  | .negativeInfinity, _ => .negativeInfinity
  | .finite _, .positiveInfinity => .positiveInfinity
  | .finite _, .negativeInfinity => .negativeInfinity

/-- An infinity of sign `negativeInfinity` times a finite factor. -/
def Number.scaled (negativeInfinity : Bool) (factor : Value) : Number :=
  if units factor = 0 then .nan else Number.infinity (negativeInfinity != negative factor)

def Number.mul : Number → Number → Number
  | .finite a, .finite b => mulResult a b
  | .nan, _ => .nan
  | _, .nan => .nan
  | .positiveInfinity, .positiveInfinity => .positiveInfinity
  | .negativeInfinity, .negativeInfinity => .positiveInfinity
  | .positiveInfinity, .negativeInfinity => .negativeInfinity
  | .negativeInfinity, .positiveInfinity => .negativeInfinity
  | .positiveInfinity, .finite b => Number.scaled false b
  | .negativeInfinity, .finite b => Number.scaled true b
  | .finite a, .positiveInfinity => Number.scaled false a
  | .finite a, .negativeInfinity => Number.scaled true a

theorem Number.scaled_not_finite (negativeInfinity : Bool) (factor result : Value) :
    Number.scaled negativeInfinity factor ≠ .finite result := by
  unfold Number.scaled Number.infinity
  split
  · simp
  · split <;> simp

/-- A finite sum has finite operands and is their total finite-operand sum. -/
theorem Number.add_finite_iff (x y : Number) (result : Value) :
    x.add y = .finite result ↔
      ∃ a b, x = .finite a ∧ y = .finite b ∧ addResult a b = .finite result := by
  cases x <;> cases y <;> simp [Number.add]

/-- A finite product has finite operands and is their total finite-operand product. -/
theorem Number.mul_finite_iff (x y : Number) (result : Value) :
    x.mul y = .finite result ↔
      ∃ a b, x = .finite a ∧ y = .finite b ∧ mulResult a b = .finite result := by
  cases x <;> cases y <;> simp [Number.mul, Number.scaled_not_finite]

theorem addResult_finite_iff (a b result : Value) :
    addResult a b = .finite result ↔
      (-overflowUnits < units a + units b ∧ units a + units b < overflowUnits) ∧
        result = roundedAdd a b := by
  unfold addResult
  split
  · rename_i below
    simp only [reduceCtorEq, false_iff, not_and]
    intro bounded
    exact absurd below (not_le_of_gt bounded.1)
  · split
    · rename_i above
      simp only [reduceCtorEq, false_iff, not_and]
      intro bounded
      exact absurd above (not_le_of_gt bounded.2)
    · rename_i notBelow notAbove
      simp only [Number.finite.injEq]
      exact ⟨fun same => ⟨⟨lt_of_not_ge notBelow, lt_of_not_ge notAbove⟩, same.symm⟩,
        fun ⟨_, same⟩ => same.symm⟩

end Rumoca.Float64
