import RumocaFMI3.CSRunStatus

noncomputable section
namespace Rumoca.FMI3.CSRun
open CCalls CMemory
variable [CInterface] {program : Events.Program Events.Invocation}

theorem Executed.performed (executed : Executed program p heap action after status) :
    Performed program p heap action status [] after := by
  cases executed with
  | step called => exact .step ((called _).mpr rfl)
  | restart reset enter leave => exact .restart ((reset _).mpr rfl) ((enter _).mpr rfl) ((leave _).mpr rfl)

theorem Calls.executes (certified : Calls model program p buffers heap before actions after final statuses) :
    Completed program p heap actions statuses [] after := by
  induction certified with
  | nil => exact .nil
  | cons executed _ _ _ ih => exact .cons executed.performed ih

theorem Calls.determines (certified : Calls model program p buffers heap before actions finalHeap final statuses)
    (completed : Completed program p heap actions observed events after) :
    observed = statuses ∧ events = [] ∧ after = finalHeap := by
  induction completed generalizing before final finalHeap statuses with
  | nil => cases certified; exact ⟨rfl, rfl, rfl⟩
  | cons performed _ ih =>
    cases certified with
    | cons executed _ _ following =>
      obtain ⟨head, event, same⟩ := (ActionContract.silent executed).performed_status performed
      cases same
      obtain ⟨tail, noEvents, finish⟩ := ih following
      exact ⟨by simp only [head, tail], by simp only [event, noEvents, List.append_nil], finish⟩

end Rumoca.FMI3.CSRun
end
