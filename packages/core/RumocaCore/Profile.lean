import RumocaCore.Real.Binary64
import RumocaCore.Transition

/-! The target-independent unit-step numerical policy for the frozen core.
`Behavior` licenses this policy only for an equation whose complete derivative
solution set is {1}. It is not a numerical solver for arbitrary equations.
Equation equivalence can therefore be lifted through each declarative IR pass
without defining the source in terms of a backend or its execution function. -/
noncomputable section
namespace Rumoca.Profile
open Binary64 Transition

inductive Function where
  | rhs | step | sample
  deriving DecidableEq

inductive RoundedSamples : Value → Nat → Value → Prop where
  | zero : RoundedSamples x 0 x
  | succ : RoundsNearestEven (units x + oneUnits) y →
      RoundedSamples y n z → RoundedSamples x (n + 1) z

theorem rounded_samples (x : Value) (n : Nat) : RoundedSamples x n (run x n) := by
  induction n generalizing x with
  | zero => exact .zero
  | succ n ih => exact .succ (round_spec _) (ih (advance x))

theorem rounded_samples_unique (h : RoundedSamples x n y) : y = run x n := by
  induction h with
  | zero => rfl
  | @succ x z n y hr _ ih =>
    have he : z = advance x := rounding_unique hr (round_spec _)
    simpa only [run, ← he] using ih

def result (f : Function) (x : Value) (n : Nat) : Value :=
  match f with
  | .rhs => one
  | .step => advance x
  | .sample => run x n

/-- Relational rounding, independent of the executable Solve/C evaluators. -/
inductive UnitBehavior : Function → Value → Nat → Observation Value → Prop where
  | rhs : UnitBehavior .rhs x n (.terminates one)
  | step : RoundsNearestEven (units x + oneUnits) y →
      UnitBehavior .step x n (.terminates y)
  | sample : RoundedSamples x n y → UnitBehavior .sample x n (.terminates y)

theorem unit_behavior_iff : UnitBehavior f x n b ↔ b = .terminates (result f x n) := by
  constructor
  · intro hb
    cases hb with
    | rhs => rfl
    | step hr => exact congrArg Observation.terminates (rounding_unique hr (round_spec _))
    | sample hs => exact congrArg Observation.terminates (rounded_samples_unique hs)
  · rintro rfl
    cases f with
    | rhs => exact .rhs
    | step => exact .step (round_spec _)
    | sample => exact .sample (rounded_samples x n)

/-- The method's applicability condition describes the entire solution set.
Merely showing that 1 is one possible derivative would be insufficient. -/
def AdmitsUnit (equation : ℝ → Prop) : Prop := ∀ dx, equation dx ↔ dx = 1

def Behavior (equation : ℝ → Prop) (f : Function) (x : Value) (n : Nat)
    (b : Observation Value) : Prop := AdmitsUnit equation ∧ UnitBehavior f x n b

/-- Reusable lifting of a declarative pass contract to the numerical policy. -/
theorem behavior_congr (h : ∀ dx, first dx ↔ second dx) :
    Behavior first f x n b ↔ Behavior second f x n b := by
  constructor <;> rintro ⟨ha, hb⟩
  · exact ⟨fun dx => (h dx).symm.trans (ha dx), hb⟩
  · exact ⟨fun dx => (h dx).trans (ha dx), hb⟩

theorem behavior_iff (h : AdmitsUnit equation) :
    Behavior equation f x n b ↔ b = .terminates (result f x n) := by
  rw [Behavior, and_iff_right h, unit_behavior_iff]

end Rumoca.Profile
