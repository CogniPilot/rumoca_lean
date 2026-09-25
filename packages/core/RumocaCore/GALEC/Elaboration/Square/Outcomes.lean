import RumocaCore.GALEC.Elaboration.Square.Execution
import RumocaCore.Array.Numerical

/-! The two total outcomes of the lowered checked DoStep body under finite
binary64 arithmetic, where a product or sum outside the finite range has no
result and `isFinite` is therefore the existence of a result. From a store
with no signal set: when every product `u[k] * u[k]` and every sum
`u[k] + u[k]` is finite, no signal is set and the store is exactly the existing
square/AD update; otherwise `OVERFLOW` is set and the store is unchanged, with
an independent real overflow witness at a failing coordinate. The sum is
checked on its own; no finite-square-to-finite-sum fact is used. -/
noncomputable section
namespace Rumoca.GALEC.Elaboration.Square
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor Coefficients VectorBodies

/-- Every product and every sum of the input coordinates is finite. -/
def Checked (input : Value Binary64.Value ⟨[extent]⟩) : Prop :=
  ∀ i : Fin extent,
    squaredInput.inDomain input[vectorIndex i] ∧ doubledInput.inDomain input[vectorIndex i]

theorem squared_inDomain (x : Binary64.Value) :
    squaredInput.inDomain x ↔ Binary64.finiteProduct x x := by
  simp only [squaredInput, ScalarExpr.inDomain, ScalarExpr.eval, true_and]
  rfl

theorem doubled_inDomain (x : Binary64.Value) :
    doubledInput.inDomain x ↔
      -Binary64.overflowUnits < Binary64.units x + Binary64.units x ∧
        Binary64.units x + Binary64.units x < Binary64.overflowUnits := by
  simp only [doubledInput, ScalarExpr.inDomain, ScalarExpr.eval, true_and]
  rfl

theorem forall_vectorIndex {P : Fin (Shape.mk [extent]).volume → Prop} :
    (∀ i : Fin extent, P (vectorIndex i)) ↔ ∀ j, P j := by
  simp only [vectorIndex_reindex]
  exact (finCongr (by simp [Shape.volume] : (Shape.mk [extent]).volume = extent)).symm.forall_congr_right

/-- The check is exactly the total encoded detector of both operations. -/
theorem checked_iff (input : Value Binary64.Value ⟨[extent]⟩) :
    Checked input ↔ Numerical.allFinite (Numerical.multiply input input) = true ∧
      Numerical.allFinite (Numerical.add input input) = true := by
  rw [Numerical.multiply_allFinite_iff, Numerical.add_allFinite_iff]
  simp only [Checked, squared_inDomain, doubled_inDomain]
  rw [forall_and]
  exact and_congr (forall_vectorIndex (P := fun j => Binary64.finiteProduct input[j] input[j]))
    (forall_vectorIndex (P := fun j => -Binary64.overflowUnits < Binary64.units input[j] +
      Binary64.units input[j] ∧ Binary64.units input[j] + Binary64.units input[j] <
        Binary64.overflowUnits))

/-- A failed check has a real witness: a coordinate whose square reaches the
overflow threshold or whose sum reaches either threshold. -/
theorem unchecked_witness (input : Value Binary64.Value ⟨[extent]⟩) :
    ¬ Checked input ↔ ∃ i : Fin extent,
      Binary64.overflowValue ≤
          Binary64.value input[vectorIndex i] * Binary64.value input[vectorIndex i] ∨
        Binary64.value input[vectorIndex i] + Binary64.value input[vectorIndex i] ≤
          -Binary64.overflowValue ∨
        Binary64.overflowValue ≤
          Binary64.value input[vectorIndex i] + Binary64.value input[vectorIndex i] := by
  simp only [Checked, not_forall]
  apply exists_congr
  intro i
  rw [squared_inDomain, doubled_inDomain, Binary64.finiteProduct_real,
    ← Binary64.sum_above_negative_overflow, ← Binary64.sum_below_overflow]
  have nonnegative := mul_self_nonneg (Binary64.value input[vectorIndex i])
  have positive := Binary64.overflowValue_pos
  simp only [Binary64.overflowValue, neg_div] at *
  constructor
  · intro failed
    by_contra none
    push Not at none
    exact failed ⟨⟨by linarith, none.1⟩, none.2.1, none.2.2⟩
  · rintro (square | low | high) ⟨⟨_, below⟩, lower, upper⟩
    · linarith
    · linarith
    · linarith

theorem union_overflow_twice (set : SignalSet) :
    (set.union overflowSet).union overflowSet = set.union overflowSet :=
  SignalSet.ext fun signal => by simp

theorem empty_union (set : SignalSet) : SignalSet.empty.union set = set :=
  SignalSet.ext fun signal => by simp

theorem overflow_reraised :
    ((SignalSet.empty.union overflowSet).diff overflowSet).union overflowSet = overflowSet :=
  SignalSet.ext fun signal => by cases signal <;> decide

theorem overflow_meets : SignalSet.Meets overflowSet (SignalSet.empty.union overflowSet) :=
  ⟨.overflow, rfl, rfl⟩

theorem empty_misses : ¬ SignalSet.Meets overflowSet SignalSet.empty := by
  rintro ⟨signal, _, present⟩
  simp at present

/-- One guard: a satisfied finiteness check leaves the state unchanged; a
failed check sets `OVERFLOW`. -/
theorem guard_runs (expression : ScalarExpr) (source : Ref inputs ⟨[extent]⟩)
    (input : Env Binary64.Value inputs) (env : IteratorEnv bounds) (i : Fin extent)
    (before after : Signaled Binary64.Value outputs) :
    (loweredGuard (expression.toTerm source vectorSubscripts)).Runs Finite.Result (fun _ => True)
        Binary64.positiveZero Binary64.one @input (IteratorEnv.push i @env) before after ↔
      (expression.inDomain (input source)[vectorIndex i] ∧ after = before) ∨
      (¬ expression.inDomain (input source)[vectorIndex i] ∧
        after = ⟨before.1, before.2.union overflowSet⟩) := by
  have holds : (Condition.finite (outputs := outputs) (expression.toTerm source vectorSubscripts)).Holds
      Finite.Result (fun _ => True) Binary64.positiveZero Binary64.one @input before
      (IteratorEnv.push i @env) ↔ expression.inDomain (input source)[vectorIndex i] := by
    simp only [Condition.Holds, and_true]
    constructor
    · rintro ⟨result, evaluated⟩
      exact ((expression.executes_iff _ _).mp
        ((expression.toTerm_executes source vectorSubscripts @input @before.1 _ result).mp evaluated)).1
    · intro domain
      exact ⟨_, (expression.toTerm_executes source vectorSubscripts @input @before.1 _ _).mpr
        ((expression.executes_iff _ _).mpr ⟨domain, rfl⟩)⟩
  simp only [loweredGuard, Statement.Runs, Condition.enter, holds, exists_eq_left]

/-- The preflight step at one index: it keeps the state when both checks
succeed and adds `OVERFLOW` otherwise. It writes no storage. -/
def Pass (input : Value Binary64.Value ⟨[extent]⟩) (i : Fin extent) : Prop :=
  squaredInput.inDomain input[vectorIndex i] ∧ doubledInput.inDomain input[vectorIndex i]

open Classical in
def preflightStep (input : Value Binary64.Value ⟨[extent]⟩) (i : Fin extent)
    (state : Signaled α outputs) : Signaled α outputs :=
  if Pass input i then state else ⟨state.1, state.2.union overflowSet⟩

theorem preflightStep_pass (passed : Pass input i) (state : Signaled α outputs) :
    preflightStep input i state = state := by
  simp only [preflightStep, if_pos passed]

theorem preflightStep_fail (failed : ¬ Pass input i) (state : Signaled α outputs) :
    preflightStep input i state = ⟨state.1, state.2.union overflowSet⟩ := by
  simp only [preflightStep, if_neg failed]

theorem preflight_body_runs (source : Ref inputs ⟨[extent]⟩) (input : Env Binary64.Value inputs)
    (env : IteratorEnv bounds) (i : Fin extent) (before after : Signaled Binary64.Value outputs) :
    (Statement.seq (loweredGuard (squaredInput.toTerm source vectorSubscripts))
        (.seq (loweredGuard (doubledInput.toTerm source vectorSubscripts)) .skip)).Runs
        Finite.Result (fun _ => True) Binary64.positiveZero Binary64.one @input
        (IteratorEnv.push i @env) before after ↔
      after = preflightStep (input source) i before := by
  change (∃ middle, (loweredGuard (squaredInput.toTerm source vectorSubscripts)).Runs _ _ _ _ _ _
      before middle ∧ ∃ next, (loweredGuard (doubledInput.toTerm source vectorSubscripts)).Runs
      _ _ _ _ _ _ middle next ∧ after = next) ↔ _
  simp only [guard_runs]
  by_cases square : squaredInput.inDomain (input source)[vectorIndex i] <;>
    by_cases sum : doubledInput.inDomain (input source)[vectorIndex i]
  · rw [preflightStep_pass ⟨square, sum⟩]
    simp only [square, sum, true_and, not_true_eq_false, false_and, or_false, exists_eq_left]
  · rw [preflightStep_fail (fun passed => sum passed.2)]
    simp only [square, sum, true_and, not_true_eq_false, false_and, or_false, false_or,
      not_false_eq_true, exists_eq_left]
  · rw [preflightStep_fail (fun passed => square passed.1)]
    simp only [square, sum, true_and, false_and, false_or, not_false_eq_true, or_false,
      not_true_eq_false, exists_eq_left]
  · rw [preflightStep_fail (fun passed => square passed.1)]
    simp only [square, sum, false_and, false_or, not_false_eq_true, true_and, exists_eq_left]
    constructor
    · rintro rfl
      exact Prod.ext rfl (union_overflow_twice _)
    · rintro rfl
      exact Prod.ext rfl (union_overflow_twice _).symm

theorem preflight_prefix (input : Value Binary64.Value ⟨[extent]⟩)
    (before : Signaled α outputs) (count : Nat) (within : count ≤ extent) :
    ((∀ i : Fin extent, i.val < count → Pass input i) ∧
        Iteration.runPrefix (preflightStep input) count within before = before) ∨
      ((¬ ∀ i : Fin extent, i.val < count → Pass input i) ∧
        Iteration.runPrefix (preflightStep input) count within before =
          ⟨before.1, before.2.union overflowSet⟩) := by
  induction count with
  | zero => exact Or.inl ⟨fun i below => absurd below (Nat.not_lt_zero _), rfl⟩
  | succ count ih =>
    rw [Iteration.runPrefix]
    by_cases last : Pass input ⟨count, within⟩
    · rw [preflightStep_pass last]
      rcases ih (Nat.le_trans (Nat.le_succ count) within) with ⟨earlier, same⟩ | ⟨earlier, same⟩
      · refine Or.inl ⟨fun i below => ?_, same⟩
        by_cases at_last : i.val = count
        · have : i = ⟨count, within⟩ := Fin.ext at_last
          exact this ▸ last
        · exact earlier i (by omega)
      · exact Or.inr ⟨fun all => earlier fun i below => all i (by omega), same⟩
    · rw [preflightStep_fail last]
      refine Or.inr ⟨fun all => last (all ⟨count, within⟩ (Nat.lt_succ_self count)), ?_⟩
      rcases ih (Nat.le_trans (Nat.le_succ count) within) with ⟨_, same⟩ | ⟨_, same⟩
      · rw [same]
      · rw [same]
        exact Prod.ext rfl (union_overflow_twice _)

/-- The whole read-only preflight: unchanged when every check succeeds, and
otherwise `OVERFLOW` added to the signal set; the store is never written. -/
theorem preflight_runs (source : Ref inputs ⟨[extent]⟩) (input : Env Binary64.Value inputs)
    (env : IteratorEnv bounds) (before after : Signaled Binary64.Value outputs) :
    (loweredPreflight (outputs := outputs) source).Runs Finite.Result (fun _ => True)
        Binary64.positiveZero Binary64.one @input @env before after ↔
      (Checked (input source) ∧ after = before) ∨
      (¬ Checked (input source) ∧ after = ⟨before.1, before.2.union overflowSet⟩) := by
  change Iteration.Executes _ extent before after ↔ _
  rw [Iteration.run_correct (preflightStep (input source)) _
    (fun i current next => preflight_body_runs source input env i current next) before after,
    Iteration.run]
  have all : (∀ i : Fin extent, i.val < extent → Pass (input source) i) ↔ Checked (input source) :=
    ⟨fun all i => all i i.isLt, fun checked i _ => checked i⟩
  rcases preflight_prefix (input source) before extent (Nat.le_refl _) with
    ⟨passed, same⟩ | ⟨failed, same⟩
  · rw [same]
    have checked := all.mp passed
    exact ⟨fun h => Or.inl ⟨checked, h⟩, fun h => h.elim (fun h => h.2) (fun h => absurd checked h.1)⟩
  · rw [same]
    have unchecked : ¬ Checked (input source) := fun checked => failed (all.mpr checked)
    exact ⟨fun h => Or.inr ⟨unchecked, h⟩,
      fun h => h.elim (fun h => absurd h.1 unchecked) (fun h => h.2)⟩

theorem square_signalFree (source : Ref inputs ⟨[extent]⟩) (rhs : Ref outputs ⟨[extent]⟩)
    (jacobian : Ref outputs (matrixShape extent extent)) :
    (loweredSquare (bounds := bounds) source rhs jacobian).SignalFree := by
  simp [loweredSquare, loweredPointwise, loweredClear, loweredScatter, Statement.SignalFree]

/-- The re-raising check: when `OVERFLOW` is set it is unset and set again;
otherwise the square body runs with the signal set kept. -/
theorem reraise_runs (source : Ref inputs ⟨[extent]⟩) (rhs : Ref outputs ⟨[extent]⟩)
    (jacobian : Ref outputs (matrixShape extent extent)) (input : Env Binary64.Value inputs)
    (env : IteratorEnv bounds) (middle after : Signaled Binary64.Value outputs) :
    (Statement.branch (.signalIn overflowSet) (.seq (.signal overflowSet) .skip)
        (loweredSquare source rhs jacobian)).Runs Finite.Result (fun _ => True)
        Binary64.positiveZero Binary64.one @input @env middle after ↔
      (SignalSet.Meets overflowSet middle.2 ∧
          after = ⟨middle.1, (middle.2.diff overflowSet).union overflowSet⟩) ∨
      (¬ SignalSet.Meets overflowSet middle.2 ∧
        (loweredSquare source rhs jacobian).Executes Finite.Result Binary64.positiveZero
          Binary64.one @input @env @middle.1 @after.1 ∧ after.2 = middle.2) := by
  change (Condition.Holds _ _ _ _ _ _ _ (.signalIn overflowSet) ∧ ∃ next, next = _ ∧ after = next) ∨
      (¬ Condition.Holds _ _ _ _ _ _ _ (.signalIn overflowSet) ∧
        (loweredSquare source rhs jacobian).Runs _ _ _ _ _ _ _ _) ↔ _
  rw [Statement.signalFree_executes _ (square_signalFree source rhs jacobian)]
  simp only [Condition.Holds, Condition.enter, exists_eq_left]

/-- The two total outcomes of the checked DoStep body from a store with no
signal set. The finite outcome is exactly the existing square/AD update. -/
theorem checked_outcomes (source : Ref inputs ⟨[extent]⟩) (rhsTarget : Ref outputs ⟨[extent]⟩)
    (jacobian : Ref outputs (matrixShape extent extent)) (state : Value Binary64.Value ⟨[extent]⟩)
    (input : Env Binary64.Value inputs) (env : IteratorEnv bounds)
    (before : Env Binary64.Value outputs) (after : Signaled Binary64.Value outputs) :
    (loweredChecked source rhsTarget jacobian).Runs Finite.Result (fun _ => True)
        Binary64.positiveZero Binary64.one @input @env ⟨@before, SignalSet.empty⟩ after ↔
      (Checked (input source) ∧ after.2 = SignalSet.empty ∧
        ∃ rhs, Finite.Executes (Rumoca.ArrayProfile.squareProgram ⟨[extent]⟩)
          (Rumoca.ArrayProfile.environment state (input source)) rhs ∧
          @after.1 = @Env.update Binary64.Value outputs (matrixShape extent extent)
            (Env.update before rhsTarget rhs) jacobian
            (diagonalValue Finite.ops Binary64.positiveZero Binary64.one doubledInput (input source))) ∨
      (¬ Checked (input source) ∧ after = ⟨@before, overflowSet⟩) := by
  change (∃ middle, (loweredPreflight source).Runs _ _ _ _ _ _ _ middle ∧ ∃ next,
    (Statement.branch (.signalIn overflowSet) (.seq (.signal overflowSet) .skip)
      (loweredSquare source rhsTarget jacobian)).Runs _ _ _ _ _ _ middle next ∧
    after = next) ↔ _
  constructor
  · rintro ⟨middle, pre, next, ran, same⟩
    subst same
    rcases (preflight_runs source input env _ middle).mp pre with ⟨checked, entered⟩ | ⟨unchecked, entered⟩
    · subst entered
      rcases (reraise_runs source rhsTarget jacobian input env _ _).mp ran with
        ⟨meets, _⟩ | ⟨_, data, kept⟩
      · exact absurd meets empty_misses
      · have body := (square_equivalent source rhsTarget jacobian Finite.Result Binary64.positiveZero
          Binary64.one @input @env @before @after.1).mp data
        exact Or.inl ⟨checked, kept,
          (SquareBodies.body_executes source rhsTarget jacobian state @input @env @before @after.1).mp body⟩
    · subst entered
      rcases (reraise_runs source rhsTarget jacobian input env _ _).mp ran with
        ⟨_, raised⟩ | ⟨missed, _⟩
      · refine Or.inr ⟨unchecked, ?_⟩
        rw [raised]
        exact Prod.ext rfl overflow_reraised
      · exact absurd overflow_meets missed
  · rintro (⟨checked, kept, rhs, executed, updated⟩ | ⟨unchecked, same⟩)
    · refine ⟨_, (preflight_runs source input env _ _).mpr (Or.inl ⟨checked, rfl⟩), after, ?_, rfl⟩
      refine (reraise_runs source rhsTarget jacobian input env _ _).mpr (Or.inr ⟨empty_misses, ?_, kept⟩)
      exact (square_equivalent source rhsTarget jacobian Finite.Result Binary64.positiveZero
        Binary64.one @input @env @before @after.1).mpr
        ((SquareBodies.body_executes source rhsTarget jacobian state @input @env @before @after.1).mpr
          ⟨rhs, executed, updated⟩)
    · refine ⟨_, (preflight_runs source input env _ _).mpr (Or.inr ⟨unchecked, rfl⟩), after, ?_, rfl⟩
      refine (reraise_runs source rhsTarget jacobian input env _ _).mpr (Or.inl ⟨overflow_meets, ?_⟩)
      rw [same]
      exact Prod.ext rfl overflow_reraised.symm

/-- Totality: every finite input has an outcome of the checked body. -/
theorem checked_total (source : Ref inputs ⟨[extent]⟩) (rhsTarget : Ref outputs ⟨[extent]⟩)
    (jacobian : Ref outputs (matrixShape extent extent)) (state : Value Binary64.Value ⟨[extent]⟩)
    (input : Env Binary64.Value inputs) (env : IteratorEnv bounds)
    (before : Env Binary64.Value outputs) :
    ∃ after, (loweredChecked source rhsTarget jacobian).Runs Finite.Result (fun _ => True)
        Binary64.positiveZero Binary64.one @input @env ⟨@before, SignalSet.empty⟩ after := by
  by_cases checked : Checked (input source)
  · have products := ((checked_iff (input source)).mp checked).1
    rw [← Numerical.allFiniteBits_encode] at products
    obtain ⟨rhs, executed⟩ :=
      (Rumoca.ArrayProfile.square_detection_finite_execution state (input source)).mp products
    exact ⟨⟨_, SignalSet.empty⟩, (checked_outcomes source rhsTarget jacobian state input env before _).mpr
      (Or.inl ⟨checked, rfl, rhs, executed, rfl⟩)⟩
  · exact ⟨_, (checked_outcomes source rhsTarget jacobian state input env before _).mpr
      (Or.inr ⟨checked, rfl⟩)⟩

end Rumoca.GALEC.Elaboration.Square
end
