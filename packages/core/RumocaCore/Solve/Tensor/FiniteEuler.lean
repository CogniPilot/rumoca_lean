import RumocaCore.Solve.FiniteEuler

/-! Proof-only, shape-parametric fixed-rate finite Euler intervals. No compiler
lowering or backend dependency. Nat counts bound arithmetic obligations only;
they do not establish public-clock termination or progress of rounded +1.
The rate is a supplied finite increment, not a proved prepared RHS or h*f. -/
noncomputable section
namespace Rumoca.Solve.TensorFiniteEuler
open Rumoca.Tensor

abbrev State (shape : Shape) := Value Binary64.Value shape

/-- Independent whole-tensor execution: each step requires finite additions. -/
inductive Prefix (initial rate : State shape) : Nat → State shape → Prop where
  | zero : Prefix initial rate 0 initial
  | next {n before after} : Prefix initial rate n before →
      Tensor.Finite.Pointwise .add before rate after →
      Prefix initial rate (n + 1) after

/-- Comparison recurrence only; post-overflow values are not executions. -/
def trajectory (initial rate : State shape) : Nat → State shape
  | 0 => initial
  | n + 1 => Value.zipWith Binary64.roundedAdd (trajectory initial rate n) rate

def IntervalDomain (initial rate : State shape) (n : Nat) : Prop :=
  ∀ k < n, ∀ i : Fin shape.volume,
    Tensor.Finite.Domain .add (trajectory initial rate k)[i] rate[i]

/-- A coordinate reaches a finite prefix and then a real overflow. No state
after that overflow is used as an operand or a reachable witness. -/
def Failure (initial rate : State shape) (n : Nat) : Prop :=
  ∃ i : Fin shape.volume, ∃ k < n, ∃ before,
    FiniteEuler.Prefix initial[i] rate[i] k before ∧ FiniteEuler.Overflow before rate[i]

theorem trajectory_get (initial rate : State shape) (n : Nat)
    (i : Fin shape.volume) :
    (trajectory initial rate n)[i] = FiniteEuler.trajectory initial[i] rate[i] n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (Value.getElem_zipWith _ _ _ i.isLt).trans
      (congrArg (fun x => Binary64.roundedAdd x rate[i]) ih)

theorem prefix_iff_coordinates (initial rate after : State shape) (n : Nat) :
    Prefix initial rate n after ↔
      ∀ i : Fin shape.volume, FiniteEuler.Prefix initial[i] rate[i] n after[i] := by
  constructor
  · intro h
    induction h with
    | zero => intro i; exact .zero
    | next _ added ih =>
      intro i
      exact .next (ih i) ((FiniteEuler.adds_iff_tensor_result _ _ _).mpr (added i))
  · induction n generalizing after with
    | zero =>
      intro h
      have same : after = initial := by
        apply Value.ext
        intro i hi
        exact ((FiniteEuler.prefix_iff_trajectory _ _ _ _).mp (h ⟨i, hi⟩)).1
      subst after
      exact .zero
    | succ n ih =>
      intro h
      have parts (i : Fin shape.volume) :=
        (FiniteEuler.prefix_succ_iff _ _ _ _).mp (h i)
      apply Prefix.next (before := trajectory initial rate n)
      · apply ih
        intro i
        obtain ⟨before, hp, _⟩ := parts i
        have eq := ((FiniteEuler.prefix_iff_trajectory _ _ _ _).mp hp).1
        simpa only [trajectory_get, eq] using hp
      · intro i
        obtain ⟨before, hp, added⟩ := parts i
        have eq := ((FiniteEuler.prefix_iff_trajectory _ _ _ _).mp hp).1
        apply (FiniteEuler.adds_iff_tensor_result _ _ _).mp
        simpa only [trajectory_get, eq] using added

theorem prefix_iff_trajectory (initial rate after : State shape) (n : Nat) :
    Prefix initial rate n after ↔
      after = trajectory initial rate n ∧ IntervalDomain initial rate n := by
  rw [prefix_iff_coordinates]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · apply Value.ext
      intro i hi
      exact (((FiniteEuler.prefix_iff_trajectory _ _ _ _).mp (h ⟨i, hi⟩)).1).trans
        (trajectory_get initial rate n ⟨i, hi⟩).symm
    · intro k hk i
      simpa only [trajectory_get] using
        ((FiniteEuler.prefix_iff_trajectory _ _ _ _).mp (h i)).2 k hk
  · rintro ⟨rfl, domain⟩ i
    apply (FiniteEuler.prefix_iff_trajectory _ _ _ _).mpr
    refine ⟨trajectory_get _ _ _ _, ?_⟩
    intro k hk
    simpa only [trajectory_get] using domain k hk i

theorem prefix_unique (ha : Prefix initial rate n a) (hb : Prefix initial rate n b) :
    a = b :=
  ((prefix_iff_trajectory _ _ _ _).mp ha).1.trans
    ((prefix_iff_trajectory _ _ _ _).mp hb).1.symm

theorem prefix_exists_iff (initial rate : State shape) (n : Nat) :
    (∃ after, Prefix initial rate n after) ↔ IntervalDomain initial rate n := by
  constructor
  · rintro ⟨after, h⟩; exact ((prefix_iff_trajectory _ _ _ _).mp h).2
  · intro h; exact ⟨_, (prefix_iff_trajectory _ _ _ _).mpr ⟨rfl, h⟩⟩

theorem failure_iff (initial rate : State shape) (n : Nat) :
    Failure initial rate n ↔ ¬ IntervalDomain initial rate n := by
  classical
  constructor
  · rintro ⟨i, k, hk, before, hp, overflow⟩ domain
    have whole := (prefix_iff_trajectory initial rate _ n).mpr ⟨rfl, domain⟩
    exact FiniteEuler.outcomes_exclusive initial[i] rate[i] n
      ⟨⟨_, (prefix_iff_coordinates _ _ _ _).mp whole i⟩,
        ⟨k, hk, before, hp, overflow⟩⟩
  · intro outside
    by_contra noFailure
    apply outside
    intro k hk i
    cases h : FiniteEuler.run initial[i] rate[i] n with
    | none =>
      exact False.elim (noFailure ⟨i, (FiniteEuler.failure_iff _ _ _).mp h⟩)
    | some after =>
      simpa only [trajectory_get] using
        ((FiniteEuler.success_iff_trajectory _ _ _ _).mp h).2 k hk

/-- Total and exclusive bounded outcomes, with a unique finite tensor result. -/
theorem total_outcomes (initial rate : State shape) (n : Nat) :
    ((∃! after, Prefix initial rate n after) ∧ ¬ Failure initial rate n) ∨
      (Failure initial rate n ∧ ¬ ∃ after, Prefix initial rate n after) := by
  classical
  by_cases domain : IntervalDomain initial rate n
  · obtain ⟨after, hp⟩ := (prefix_exists_iff _ _ _).mpr domain
    exact Or.inl ⟨⟨after, hp, fun _ h => prefix_unique h hp⟩,
      fun h => (failure_iff _ _ _).mp h domain⟩
  · exact Or.inr ⟨(failure_iff _ _ _).mpr domain,
      fun h => domain ((prefix_exists_iff _ _ _).mp h)⟩

/-- Coordinate rejection is equivalent to overflow at a globally reachable
whole-tensor boundary. Bounded induction moves an earlier failure backward
until every coordinate has a finite prefix at the chosen step. -/
theorem failure_boundary (initial rate : State shape) (n : Nat) :
    Failure initial rate n ↔
      ∃ k < n, ∃ before : State shape, Prefix initial rate k before ∧
        ∃ i : Fin shape.volume, FiniteEuler.Overflow before[i] rate[i] := by
  classical
  constructor
  · induction n with
    | zero =>
      rintro ⟨i, k, hk, _⟩
      omega
    | succ n ih =>
      intro failed
      by_cases earlier : Failure initial rate n
      · obtain ⟨k, hk, before, hp, overflow⟩ := ih earlier
        exact ⟨k, by omega, before, hp, overflow⟩
      · obtain ⟨⟨before, hp, _⟩, _⟩ | ⟨bad, _⟩ := total_outcomes initial rate n
        · obtain ⟨i, k, hk, scalarBefore, scalarPrefix, overflow⟩ := failed
          have equal : k = n := by
            by_contra different
            exact earlier ⟨i, k, by omega, scalarBefore, scalarPrefix, overflow⟩
          subst k
          have coordinate := (prefix_iff_coordinates _ _ _ _).mp hp i
          have same : scalarBefore = before[i] :=
            ((FiniteEuler.prefix_iff_trajectory _ _ _ _).mp scalarPrefix).1.trans
              ((FiniteEuler.prefix_iff_trajectory _ _ _ _).mp coordinate).1.symm
          exact ⟨n, by omega, before, hp, i, same ▸ overflow⟩
        · exact False.elim (earlier bad)
  · rintro ⟨k, hk, before, hp, i, overflow⟩
    exact ⟨i, k, hk, before[i], (prefix_iff_coordinates _ _ _ _).mp hp i, overflow⟩

/-- Exactly the bounded whole-tensor step premises needed for loop composition. -/
theorem prefix_iff_path (initial rate after : State shape) (n : Nat) :
    Prefix initial rate n after ↔
      ∃ states : Nat → State shape, states 0 = initial ∧ states n = after ∧
        ∀ k < n, Tensor.Finite.Pointwise .add (states k) rate (states (k + 1)) := by
  constructor
  · intro hp
    obtain ⟨same, domain⟩ := (prefix_iff_trajectory _ _ _ _).mp hp
    refine ⟨trajectory initial rate, rfl, same.symm, ?_⟩
    intro k hk i
    apply (FiniteEuler.adds_iff_tensor_result _ _ _).mp
    apply (FiniteEuler.adds_iff_domain _ _ _).mpr
    exact ⟨domain k hk i, Value.getElem_zipWith _ _ _ i.isLt⟩
  · rintro ⟨states, first, last, steps⟩
    have hp : Prefix (states 0) rate n (states n) := by
      clear last
      induction n with
      | zero => exact .zero
      | succ n ih =>
        exact .next (ih (fun k hk => steps k (by omega))) (steps n (by omega))
    simpa only [first, last] using hp

theorem zero_steps (initial rate after : State shape) :
    Prefix initial rate 0 after ↔ after = initial := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .zero

/-- Zero-volume shapes succeed for every count, with their unique empty value. -/
theorem empty_interval (initial rate : State shape) (empty : shape.volume = 0)
    (n : Nat) : Prefix initial rate n initial ∧ ¬ Failure initial rate n := by
  constructor
  · apply (prefix_iff_coordinates _ _ _ _).mpr
    intro i
    exact False.elim (by have := i.isLt; omega)
  · rintro ⟨i, _⟩
    have := i.isLt
    omega

end Rumoca.Solve.TensorFiniteEuler
