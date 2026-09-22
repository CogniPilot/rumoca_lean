import RumocaCore.Real.AdditionResult
import RumocaCore.Solve.Tensor.Finite

/-! Finite scalar Euler interval semantics. No emitted C, source admission or FMI policy.
The evaluator is proof-only and noncomputable. Its structural iteration keeps
only finite scalar states; a rejected result is never an arithmetic operand.
Nat is an abstract iteration count, not a public CS clock interval. Count
conversion, clock progress/finiteness and actual while guards are not modeled.
The existing tensor finite-addition domain and independent Adds relation are
reused rather than defining another rounding or floating-point semantics. -/
noncomputable section
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
namespace Rumoca.Solve.FiniteEuler
open Binary64

/-- A finite execution prefix, specified independently of the evaluator. -/
inductive Prefix (initial rate : Binary64.Value) : Nat → Binary64.Value → Prop where
  | zero : Prefix initial rate 0 initial
  | next {n before after} : Prefix initial rate n before →
      Adds before rate (.finite after) → Prefix initial rate (n + 1) after

/-- Exact real overflow threshold, including both signs and threshold ties. -/
def Overflow (before rate : Binary64.Value) : Prop :=
  value before + value rate ≤ -overflowValue ∨
    overflowValue ≤ value before + value rate

/-- Finite operands are checked before a result can become another operand.
The NaN arm is unreachable, as proved by addResult_no_nan. -/
def checkedAdd (before rate : Binary64.Value) : Option Binary64.Value :=
  match addResult before rate with
  | .finite after => some after
  | _ => none

def run (initial rate : Binary64.Value) : Nat → Option Binary64.Value
  | 0 => some initial
  | n + 1 => (run initial rate n).bind (fun before => checkedAdd before rate)

/-- The ordinary rounded recurrence is a comparison object. Its values after
overflow are not asserted to be numerical executions. -/
def trajectory (initial rate : Binary64.Value) : Nat → Binary64.Value
  | 0 => initial
  | n + 1 => roundedAdd (trajectory initial rate n) rate

def IntervalDomain (initial rate : Binary64.Value) (n : Nat) : Prop :=
  ∀ k < n, Tensor.Finite.Domain .add (trajectory initial rate k) rate

def Failure (initial rate : Binary64.Value) (n : Nat) : Prop :=
  ∃ k < n, ∃ before, Prefix initial rate k before ∧ Overflow before rate

theorem checkedAdd_some_iff (before rate after : Binary64.Value) :
    checkedAdd before rate = some after ↔ Adds before rate (.finite after) := by
  rw [← addResult_correct]
  unfold checkedAdd
  cases addResult before rate <;> simp

theorem checkedAdd_none_iff (before rate : Binary64.Value) :
    checkedAdd before rate = none ↔ Overflow before rate := by
  have spec := addResult_spec before rate
  unfold checkedAdd
  cases h : addResult before rate with
  | finite after =>
    rw [h] at spec
    simp only [Adds] at spec
    simp only [Option.some_ne_none, false_iff, Overflow, not_or]
    exact ⟨not_le_of_gt spec.1, not_le_of_gt spec.2.1⟩
  | negativeInfinity =>
    rw [h] at spec
    exact ⟨fun _ => Or.inl spec, fun _ => rfl⟩
  | positiveInfinity =>
    rw [h] at spec
    exact ⟨fun _ => Or.inr spec, fun _ => rfl⟩
  | nan => exact False.elim (addResult_no_nan before rate h)

theorem adds_iff_domain (before rate after : Binary64.Value) :
    Adds before rate (.finite after) ↔
      Tensor.Finite.Domain .add before rate ∧ after = roundedAdd before rate := by
  constructor
  · intro h
    exact ⟨⟨(sum_above_negative_overflow before rate).mp h.1,
      (sum_below_overflow before rate).mp h.2.1⟩,
      sum_rounding_unique h.2.2 (roundedAdd_spec before rate)⟩
  · rintro ⟨domain, rfl⟩
    exact (addResult_correct _ _ _).mp (addResult_finite before rate domain)

theorem prefix_succ_iff (initial rate after : Binary64.Value) (n : Nat) :
    Prefix initial rate (n + 1) after ↔
      ∃ before, Prefix initial rate n before ∧ Adds before rate (.finite after) := by
  constructor
  · intro h
    cases h with
    | next executed added => exact ⟨_, executed, added⟩
  · rintro ⟨before, executed, added⟩
    exact .next executed added

theorem success_iff (initial rate after : Binary64.Value) (n : Nat) :
    run initial rate n = some after ↔ Prefix initial rate n after := by
  induction n generalizing after with
  | zero =>
    constructor
    · intro h; have same : initial = after := Option.some.inj h
      subst after; exact .zero
    · intro h; cases h; rfl
  | succ n ih =>
    rw [prefix_succ_iff]
    simp only [run, Option.bind_eq_some_iff, checkedAdd_some_iff, ih]

theorem prefix_iff_trajectory (initial rate after : Binary64.Value) (n : Nat) :
    Prefix initial rate n after ↔
      after = trajectory initial rate n ∧ IntervalDomain initial rate n := by
  induction n generalizing after with
  | zero =>
    constructor
    · intro h; cases h; exact ⟨rfl, by intro k hk; omega⟩
    · rintro ⟨rfl, _⟩; exact .zero
  | succ n ih =>
    rw [prefix_succ_iff]
    constructor
    · rintro ⟨before, executed, added⟩
      obtain ⟨rfl, domain⟩ := (ih before).mp executed
      obtain ⟨last, same⟩ := (adds_iff_domain _ _ _).mp added
      refine ⟨same, ?_⟩
      intro k hk
      by_cases equal : k = n
      · subst k; exact last
      · exact domain k (by omega)
    · rintro ⟨rfl, domain⟩
      refine ⟨trajectory initial rate n, (ih _).mpr ⟨rfl, ?_⟩, ?_⟩
      · intro k hk; exact domain k (by omega)
      · exact (adds_iff_domain _ _ _).mpr ⟨domain n (by omega), rfl⟩

theorem success_iff_trajectory (initial rate after : Binary64.Value) (n : Nat) :
    run initial rate n = some after ↔
      after = trajectory initial rate n ∧ IntervalDomain initial rate n := by
  rw [success_iff, prefix_iff_trajectory]

/-- Rejection is absorbing: later structural iterations do not add to it. -/
theorem failure_persists (initial rate : Binary64.Value) {k n : Nat}
    (failed : run initial rate k = none) (le : k ≤ n) : run initial rate n = none := by
  induction n with
  | zero =>
    have equal : k = 0 := by omega
    subst k
    exact failed
  | succ n ih =>
    by_cases equal : k = n + 1
    · subst k; exact failed
    · simp only [run, ih (by omega), Option.bind_none]

theorem failure_iff (initial rate : Binary64.Value) (n : Nat) :
    run initial rate n = none ↔ Failure initial rate n := by
  constructor
  · induction n with
    | zero => simp [run]
    | succ n ih =>
      intro failed
      cases previous : run initial rate n with
      | none =>
        obtain ⟨k, hk, before, executed, overflow⟩ := ih previous
        exact ⟨k, by omega, before, executed, overflow⟩
      | some before =>
        have rejected : checkedAdd before rate = none := by
          simpa only [run, previous, Option.bind_some] using failed
        exact ⟨n, by omega, before, (success_iff _ _ _ _).mp previous,
          (checkedAdd_none_iff _ _).mp rejected⟩
  · rintro ⟨k, hk, before, executed, overflow⟩
    have failed : run initial rate (k + 1) = none := by
      simp only [run, (success_iff _ _ _ _).mpr executed, Option.bind_some,
        (checkedAdd_none_iff _ _).mpr overflow]
    exact failure_persists initial rate failed (by omega)

theorem total_outcomes (initial rate : Binary64.Value) (n : Nat) :
    (∃ after, run initial rate n = some after ∧ Prefix initial rate n after) ∨
      (run initial rate n = none ∧ Failure initial rate n) := by
  cases h : run initial rate n with
  | none => exact Or.inr ⟨rfl, (failure_iff _ _ _).mp h⟩
  | some after => exact Or.inl ⟨after, rfl, (success_iff _ _ _ _).mp h⟩

theorem outcomes_exclusive (initial rate : Binary64.Value) (n : Nat) :
    ¬ ((∃ after, Prefix initial rate n after) ∧ Failure initial rate n) := by
  rintro ⟨⟨after, executed⟩, failure⟩
  have good := (success_iff _ _ _ _).mpr executed
  rw [(failure_iff _ _ _).mpr failure] at good
  cases good

/-- A rejected interval has an actual finite prefix and a signed-infinite next
addition. No post-overflow rounded recurrence is used as a reachable witness. -/
theorem failure_boundary (initial rate : Binary64.Value) (n : Nat)
    (failed : run initial rate n = none) :
    ∃ k < n, ∃ before, Prefix initial rate k before ∧
      run initial rate k = some before ∧ run initial rate (k + 1) = none ∧
      ((Adds before rate .negativeInfinity ∧
        value before + value rate ≤ -overflowValue) ∨
       (Adds before rate .positiveInfinity ∧
        overflowValue ≤ value before + value rate)) := by
  obtain ⟨k, hk, before, executed, overflow⟩ := (failure_iff _ _ _).mp failed
  have good := (success_iff _ _ _ _).mpr executed
  refine ⟨k, hk, before, executed, good, ?_, ?_⟩
  · simp only [run, good, Option.bind_some, (checkedAdd_none_iff _ _).mpr overflow]
  · exact overflow.elim (fun h => Or.inl ⟨h, h⟩) (fun h => Or.inr ⟨h, h⟩)

/-- Direct compatibility with the existing tensor scalar instruction relation. -/
theorem adds_iff_tensor_result (before rate after : Binary64.Value) :
    Adds before rate (.finite after) ↔ Tensor.Finite.Result .add before rate after := by
  rw [Tensor.Finite.result_iff, adds_iff_domain]
  rfl

theorem prefix_of_path (rate : Binary64.Value) (states : Nat → Binary64.Value) (n : Nat)
    (steps : ∀ k < n, Adds (states k) rate (.finite (states (k + 1)))) :
    Prefix (states 0) rate n (states n) := by
  induction n with
  | zero => exact .zero
  | succ n ih =>
    exact .next (ih (fun k hk => steps k (by omega))) (steps n (by omega))

/-- Supplies the bounded per-step premises consumed by an Euler loop proof.
This deliberately says nothing about additions after the requested count. -/
theorem success_iff_path (initial rate after : Binary64.Value) (n : Nat) :
    run initial rate n = some after ↔
      ∃ states : Nat → Binary64.Value, states 0 = initial ∧ states n = after ∧
        ∀ k < n, Adds (states k) rate (.finite (states (k + 1))) := by
  constructor
  · intro good
    obtain ⟨same, domain⟩ := (success_iff_trajectory _ _ _ _).mp good
    refine ⟨trajectory initial rate, rfl, same.symm, ?_⟩
    intro k hk
    exact (adds_iff_domain _ _ _).mpr ⟨domain k hk, rfl⟩
  · rintro ⟨states, initialEq, finalEq, steps⟩
    have executed := prefix_of_path rate states n steps
    rw [initialEq, finalEq] at executed
    exact (success_iff _ _ _ _).mpr executed

/-- A universal bit-sensitive zero-sign result, not just real equality. -/
theorem negative_zero_interval (n : Nat) :
    run negativeZero negativeZero n = some negativeZero := by
  have domain : Tensor.Finite.Domain .add negativeZero negativeZero := by
    have zero : units negativeZero = 0 := by decide +kernel
    change -overflowUnits < units negativeZero + units negativeZero ∧
      units negativeZero + units negativeZero < overflowUnits
    rw [zero, add_zero]
    constructor <;> decide +kernel
  have step : checkedAdd negativeZero negativeZero = some negativeZero :=
    (checkedAdd_some_iff _ _ _).mpr ((adds_iff_domain _ _ _).mpr
      ⟨domain, roundedAdd_negative_zero.symm⟩)
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, ih, Option.bind_some, step]

end Rumoca.Solve.FiniteEuler
