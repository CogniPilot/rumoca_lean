import RumocaCore.Transition

/-! Finite prefixes preserve all observations of a deterministic machine.
This permits a local refactoring to reach a common continuation in different
numbers of steps without assuming that continuation terminates successfully. -/
namespace Rumoca.Transition.Machine
variable {S R : Type} (m : Machine S R) {s t : S} {b : Observation R}

theorem step_behaviors (step : m.step s t) : m.Behaves s b ↔ m.Behaves t b := by
  constructor
  · intro h
    cases h with
    | terminates reach final =>
      cases reach with
      | refl => exact False.elim (m.final_stuck final _ step)
      | next first rest =>
        cases m.deterministic step first
        exact .terminates rest final
    | wrong reach final stuck =>
      cases reach with
      | refl => exact False.elim (stuck _ step)
      | next first rest =>
        cases m.deterministic step first
        exact .wrong rest final stuck
    | diverges trace initial steps =>
      refine .diverges (fun n => trace (n + 1)) ?_ (fun n => steps (n + 1))
      exact m.deterministic (initial ▸ steps 0) step
  · intro h
    cases h with
    | terminates reach final => exact .terminates (.next step reach) final
    | wrong reach final stuck => exact .wrong (.next step reach) final stuck
    | diverges trace initial steps =>
      refine .diverges (fun n => match n with | 0 => s | n + 1 => trace n) rfl ?_
      intro n
      cases n with
      | zero => simpa only [initial] using step
      | succ n => exact steps n

theorem prefix_behaviors (path : Reaches m.step s t) : m.Behaves s b ↔ m.Behaves t b := by
  induction path with
  | refl => rfl
  | next first rest ih => exact (step_behaviors m first).trans ih

end Rumoca.Transition.Machine
