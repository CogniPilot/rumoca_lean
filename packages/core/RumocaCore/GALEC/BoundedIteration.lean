import RumocaCore.Tensor.Matrix

/-! Structural bounded iteration for checked GALEC execution. This is the shared
iteration mechanism for future typed statement interpretation, not a new source
construct or an IR made from opaque callbacks. The body is its already-defined
semantic interpretation. Index bounds are intrinsic, execution is ascending,
and no fuel approximation or compile-time instruction enumeration is used.

Zero-length iteration is defined mathematically; this does not license GALEC
zero-sized declarations or an unchecked `1:0` range. One-based surface indices
and target Integer representability remain separate elaboration obligations. -/
namespace Rumoca.GALEC.Iteration

/-- Execute exactly the first `count` iterations, in increasing index order. -/
def runPrefix (body : Fin bound → σ → σ) :
    (count : Nat) → count ≤ bound → σ → σ
  | 0, _, state => state
  | count + 1, within, state =>
      body ⟨count, Nat.lt_of_succ_le within⟩
        (runPrefix body count (Nat.le_trans (Nat.le_succ count) within) state)

def run (body : Fin bound → σ → σ) (state : σ) : σ :=
  runPrefix body bound (Nat.le_refl _) state

/-- Independent ordered execution relation. The body relation may be partial
or nondeterministic; the loop relation does not refer to `runPrefix` or `run`. -/
inductive Executes (step : Fin bound → σ → σ → Prop) : Nat → σ → σ → Prop where
  | zero (state) : Executes step 0 state state
  | next {count initial before after} (within : count < bound)
      (earlier : Executes step count initial before)
      (body : step ⟨count, within⟩ before after) :
      Executes step (count + 1) initial after

theorem Executes.bounded {step : Fin bound → σ → σ → Prop}
    (h : Executes step count initial final) : count ≤ bound := by
  cases h with
  | zero => omega
  | next within _ _ => omega

/-- Refinement for every body whose execution relation is implemented by the
given total function, all initial states and every in-bounds prefix. -/
theorem prefix_correct (body : Fin bound → σ → σ)
    (step : Fin bound → σ → σ → Prop)
    (body_correct : ∀ i before after, step i before after ↔ after = body i before)
    (count : Nat) (within : count ≤ bound) (initial final : σ) :
    Executes step count initial final ↔ final = runPrefix body count within initial := by
  induction count generalizing final with
  | zero =>
    constructor
    · intro h; cases h; rfl
    · intro h; subst final; exact .zero initial
  | succ count ih =>
    constructor
    · intro h
      cases h with
      | next hk earlier executed =>
        have same := (ih (Nat.le_of_lt hk) _).mp earlier
        rw [(body_correct _ _ _).mp executed, same]
        rfl
    · intro h
      subst final
      let earlierBound : count ≤ bound := Nat.le_trans (Nat.le_succ count) within
      apply Executes.next (before := runPrefix body count earlierBound initial)
        (Nat.lt_of_succ_le within)
      · exact (ih earlierBound _).mpr rfl
      · exact (body_correct _ _ _).mpr rfl

theorem run_correct (body : Fin bound → σ → σ)
    (step : Fin bound → σ → σ → Prop)
    (body_correct : ∀ i before after, step i before after ↔ after = body i before)
    (initial final : σ) :
    Executes step bound initial final ↔ final = run body initial :=
  prefix_correct body step body_correct bound (Nat.le_refl _) initial final

/-- Partial arithmetic over immutable inputs supplies an index-dependent
guard. Successful iteration retains every guard, not just evaluator equality.
State-dependent guards require a separate invariant and are not covered here. -/
theorem prefix_guarded_correct (body : Fin bound → σ → σ)
    (step : Fin bound → σ → σ → Prop) (guard : Fin bound → Prop)
    (body_correct : ∀ i before after,
      step i before after ↔ guard i ∧ after = body i before)
    (count : Nat) (within : count ≤ bound) (initial final : σ) :
    Executes step count initial final ↔
      (∀ i : Fin bound, i.val < count → guard i) ∧
      final = runPrefix body count within initial := by
  induction count generalizing final with
  | zero =>
    constructor
    · intro h; cases h; exact ⟨by intro i h; omega, rfl⟩
    · rintro ⟨_, same⟩
      change final = initial at same
      subst final
      exact .zero initial
  | succ count ih =>
    constructor
    · intro h
      cases h with
      | next hk earlier executed =>
        obtain ⟨guards, same⟩ := (ih (Nat.le_of_lt hk) _).mp earlier
        obtain ⟨lastGuard, lastSame⟩ := (body_correct _ _ _).mp executed
        constructor
        · intro i beforeEnd
          by_cases earlierIndex : i.val < count
          · exact guards i earlierIndex
          · have sameIndex : i = ⟨count, hk⟩ := by
              apply Fin.ext
              change i.val = count
              omega
            simpa only [sameIndex] using lastGuard
        · rw [lastSame, same]
          rfl
    · rintro ⟨guards, rfl⟩
      let earlierBound : count ≤ bound := Nat.le_trans (Nat.le_succ count) within
      apply Executes.next (before := runPrefix body count earlierBound initial)
        (Nat.lt_of_succ_le within)
      · exact (ih earlierBound _).mpr
          ⟨fun i hi => guards i (Nat.lt_trans hi (Nat.lt_succ_self count)), rfl⟩
      · exact (body_correct _ _ _).mpr ⟨guards _ (Nat.lt_succ_self count), rfl⟩

theorem run_guarded_correct (body : Fin bound → σ → σ)
    (step : Fin bound → σ → σ → Prop) (guard : Fin bound → Prop)
    (body_correct : ∀ i before after,
      step i before after ↔ guard i ∧ after = body i before)
    (initial final : σ) :
    Executes step bound initial final ↔
      (∀ i, guard i) ∧ final = run body initial := by
  simpa only [run, Fin.isLt, forall_const] using
    prefix_guarded_correct body step guard body_correct bound (Nat.le_refl _) initial final

theorem prefix_invariant (body : Fin bound → σ → σ) (invariant : Nat → σ → Prop)
    (initial : σ) (start : invariant 0 initial)
    (preserved : ∀ (i : Fin bound) state,
      invariant i.val state → invariant (i.val + 1) (body i state))
    (count : Nat) (within : count ≤ bound) :
    invariant count (runPrefix body count within initial) := by
  induction count with
  | zero => exact start
  | succ count ih =>
    exact preserved ⟨count, Nat.lt_of_succ_le within⟩ _ (ih _)

/-- An arbitrary observation preserved by every body is preserved by any
prefix; the result covers frames beyond a particular tensor or profile. -/
theorem prefix_frame (body : Fin bound → σ → σ) (observe : σ → β)
    (preserved : ∀ i state, observe (body i state) = observe state)
    (count : Nat) (within : count ≤ bound) (initial : σ) :
    observe (runPrefix body count within initial) = observe initial := by
  apply prefix_invariant body (fun _ state => observe state = observe initial) initial rfl
  intro i state same
  exact (preserved i state).trans same

theorem one_based_bounds (i : Fin bound) : 1 ≤ i.val + 1 ∧ i.val + 1 ≤ bound := by
  have := i.isLt
  omega

end Rumoca.GALEC.Iteration
