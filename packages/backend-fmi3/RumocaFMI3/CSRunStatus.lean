import RumocaFMI3.CSRunLogging

noncomputable section
namespace Rumoca.FMI3.CSRun
open CTree CMemory CBody StaticFactory CCalls

/-- Every actually returned status agrees with the complete action contract;
matching the reference status is a conclusion, not an execution premise. -/
theorem ActionContract.performed_status [CInterface] {program : Events.Program Events.Invocation}
    (certified : ActionContract program p heap action status returns blocked)
    (performed : Performed program p heap action observedStatus events after) :
    observedStatus = status ∧ returns events after := by
  have same : observedStatus = status := by
    cases performed with
    | step called =>
      rcases (certified.step_behaviors _).mp called with ⟨trace, next, _, same⟩ | ⟨_, impossible⟩
      · cases same
        rfl
      · cases impossible
    | restart _ _ _ =>
      cases certified with
      | silent executed => cases executed; rfl
  refine ⟨same, ?_⟩
  subst observedStatus
  exact certified.returned performed

/-- A completed actual host script determines its returned status list.
The branching certificate proves that list equals the reference list. -/
theorem LoggedTrace.statuses_eq [CInterface] {program : Events.Program Events.Invocation}
    {logger : Logger} {owners : SlotOwners.State objects.capacity}
    (certified : LoggedTrace objects logger owners model program p buffers heap before actions final statuses)
    (completed : Completed program p heap actions observedStatuses events after) :
    observedStatuses = statuses := by
  induction completed generalizing before final statuses with
  | nil => cases certified; rfl
  | cons performed rest ih =>
    cases certified with
    | cons call returned following =>
      obtain ⟨head, outcome⟩ := call.performed_status performed
      have tail := ih (following _ _ outcome)
      simp only [head, tail]

end Rumoca.FMI3.CSRun
end
