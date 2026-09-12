import RumocaCore.Transition.Events

/-! Silent prefixes preserve every observation of the continuation. A foreign
choice followed by forced termination retains every outcome, including absence. -/
namespace Rumoca.Transition.Events
variable {S E R : Type}

theorem Machine.silent_step_behaviors (m : Machine S E R)
    (step : m.step s [] t)
    (unique : ∀ events u, m.step s events u → events = [] ∧ u = t)
    (behavior : Observation E R) : m.Behaves s behavior ↔ m.Behaves t behavior := by
  constructor
  · intro observed
    cases observed with
    | terminates path done =>
        cases path with
        | refl => exact False.elim (m.final_stuck done [] t step)
        | next first rest =>
            obtain ⟨rfl, rfl⟩ := unique _ _ first
            exact .terminates rest done
    | wrong path done stuck =>
        cases path with
        | refl => exact False.elim (stuck [] t step)
        | next first rest =>
            obtain ⟨rfl, rfl⟩ := unique _ _ first
            exact .wrong rest done stuck
    | diverges states chunks initial steps history =>
        have first := unique _ _ (initial ▸ steps 0)
        exact .diverges (fun n => states (n + 1)) (fun n => chunks (n + 1)) first.2
          (fun n => steps (n + 1)) ((records_drop_silent first.1).mpr history)
  · intro observed
    cases observed with
    | terminates path done => exact .terminates (.next step path) done
    | wrong path done stuck => exact .wrong (.next step path) done stuck
    | diverges states chunks initial steps history =>
        let states' : Nat → S := fun n => match n with | 0 => s | n + 1 => states n
        let chunks' : Nat → List E := fun n => match n with | 0 => [] | n + 1 => chunks n
        refine .diverges states' chunks' rfl ?_ ?_
        · intro n
          cases n with
          | zero => simpa only [states', chunks', initial] using step
          | succ n => exact steps n
        · exact (records_drop_silent (chunks := chunks') rfl).mp history

/-- A possibly nondeterministic first step followed by a terminating silent
suffix. Missing outcomes are represented by stuck execution, not omitted.
Neither existence nor uniqueness of the first outcome is assumed. -/
theorem Machine.terminal_choices_behaviors (m : Machine S E R) (s : S)
    (unfinished : m.final s = none)
    (finished : ∀ events t, m.step s events t → ∃ result, Forced m t [] result)
    (behavior : Observation E R) :
    m.Behaves s behavior ↔
      (∃ events t result, m.step s events t ∧ Forced m t [] result ∧
        behavior = .terminates events result) ∨
      ((∀ events t, ¬ m.step s events t) ∧ behavior = .wrong []) := by
  constructor
  · intro observed
    cases observed with
    | terminates path done =>
        cases path with
        | refl => rw [unfinished] at done; contradiction
        | next first rest =>
            obtain ⟨result, forced⟩ := finished _ _ first
            have matched := forced.terminal_matches rest (m.final_stuck done)
            have same := Option.some.inj (done.symm.trans matched.2)
            exact Or.inl ⟨_, _, result, first, forced, by simp only [matched.1, List.append_nil, same]⟩
    | wrong path done stuck =>
        cases path with
        | refl => exact Or.inr ⟨stuck, rfl⟩
        | next first rest =>
            obtain ⟨result, forced⟩ := finished _ _ first
            have matched := forced.terminal_matches rest stuck
            rw [done] at matched
            cases matched.2
    | diverges states chunks initial steps history =>
        have accessible : Acc (fun t s => ∃ events, m.step s events t) s := by
          constructor
          rintro t ⟨events, step⟩
          obtain ⟨result, forced⟩ := finished events t step
          exact forced.accessible
        exact False.elim (no_infinite_of_acc accessible ⟨states, initial, fun n => ⟨chunks n, steps n⟩⟩)
  · rintro (⟨events, t, result, first, forced, rfl⟩ | ⟨stuck, rfl⟩)
    · obtain ⟨last, path, done⟩ := forced.reaches
      simpa only [List.append_nil] using Machine.Behaves.terminates (Reaches.next first path) done
    · exact .wrong (.refl _) unfinished stuck

end Rumoca.Transition.Events
