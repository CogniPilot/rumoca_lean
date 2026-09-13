import RumocaCore.Transition.Events.Choices

/-! Silent nondeterministic choices can be removed when every outcome has the
same continuation observations. Existence is required, so a missing external
outcome cannot silently become a successful continuation. -/
namespace Rumoca.Transition.Events
variable {S E R : Type}

theorem Machine.prepend_silent (m : Machine S E R) (step : m.step s [] t)
    (observed : m.Behaves t behavior) : m.Behaves s behavior := by
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

/-- Arbitrary future termination, errors and divergence are retained when all
represented silent outcomes converge observationally. -/
theorem Machine.silent_choices_behaviors (m : Machine S E R)
    (available : ∃ t, m.step s [] t)
    (silent : ∀ events t, m.step s events t → events = [])
    (equivalent : ∀ t, m.step s [] t → ∀ behavior, m.Behaves t behavior ↔ m.Behaves target behavior)
    (behavior : Observation E R) : m.Behaves s behavior ↔ m.Behaves target behavior := by
  constructor
  · intro observed
    cases observed with
    | terminates path done =>
      cases path with
      | refl => obtain ⟨t, step⟩ := available; exact False.elim (m.final_stuck done [] t step)
      | next first rest =>
        have noEvents := silent _ _ first
        subst noEvents
        exact (equivalent _ first _).mp (.terminates rest done)
    | wrong path done stuck =>
      cases path with
      | refl => obtain ⟨t, step⟩ := available; exact False.elim (stuck [] t step)
      | next first rest =>
        have noEvents := silent _ _ first
        subst noEvents
        exact (equivalent _ first _).mp (.wrong rest done stuck)
    | diverges states chunks initial steps history =>
      have first := initial ▸ steps 0
      have noEvents := silent _ _ first
      apply (equivalent _ (noEvents ▸ first) _).mp
      exact .diverges (fun n => states (n + 1)) (fun n => chunks (n + 1)) rfl
        (fun n => steps (n + 1)) ((records_drop_silent noEvents).mpr history)
  · intro observed
    obtain ⟨t, step⟩ := available
    exact m.prepend_silent step ((equivalent t step behavior).mpr observed)

end Rumoca.Transition.Events
