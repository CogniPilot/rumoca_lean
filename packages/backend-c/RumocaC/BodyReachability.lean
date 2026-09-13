import RumocaC.Body

namespace Rumoca.CBody
/-- Finite reachability and bounded evaluation describe the same executions. -/
theorem run_of_reaches [interface : CInterface] (reached : Transition.Reaches machine.step s t) :
    ∃ n, run n s = some t := by
  induction reached with
  | refl => exact ⟨0, rfl⟩
  | next step _ ih =>
    obtain ⟨n, ran⟩ := ih
    exact ⟨n + 1, by simpa only [run, show next _ = some _ from step, Option.bind_some] using ran⟩

end Rumoca.CBody
