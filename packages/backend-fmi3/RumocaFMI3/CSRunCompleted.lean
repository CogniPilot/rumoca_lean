import RumocaFMI3.CSRunStatus

noncomputable section
namespace Rumoca.FMI3.CSRun
open CCalls CMemory
variable [CInterface] {program : Events.Program Events.Invocation}

theorem Calls.executes (certified : Calls model program p buffers heap before actions after final statuses) :
    Completed program p heap actions statuses [] after := by
  induction certified with
  | nil => exact .nil
  | cons executed _ _ _ _ ih => exact .cons executed.performed ih

theorem Calls.determines (certified : Calls model program p buffers heap before actions finalHeap final statuses)
    (completed : Completed program p heap actions observed events after) :
    observed = statuses ∧ events = [] ∧ after = finalHeap := by
  induction completed generalizing before final finalHeap statuses with
  | nil => cases certified; exact ⟨rfl, rfl, rfl⟩
  | cons performed _ ih =>
    cases certified with
    | cons executed _ _ _ following =>
      obtain ⟨head, event, same⟩ := (ActionContract.silent executed).performed_status performed
      cases same
      obtain ⟨tail, noEvents, finish⟩ := ih following
      exact ⟨by simp only [head, tail], by simp only [event, noEvents, List.append_nil], finish⟩

theorem Calls.storage (certified : Calls model program p buffers heap before actions after final statuses) :
    CStorage.Preserves heap after := by
  induction certified with
  | nil => exact .refl _
  | cons _ _ _ memory _ ih => exact memory.1.trans ih

theorem Calls.atomic (certified : Calls model program p buffers heap before actions after final statuses) :
    CAtomicBoolean.Preserves heap after := by
  induction certified with
  | nil => exact .refl _
  | cons _ _ _ memory _ ih => exact memory.2.1.trans ih

theorem Calls.retains (certified : Calls model program p buffers heap before actions after final statuses) :
    Retains p heap after := by
  induction certified with
  | nil => exact fun _ _ => rfl
  | cons _ _ _ memory _ ih => exact memory.2.2.1.trans ih

/-- The complete silent-call certificate retains exact contents outside
its instance and outputs, including borrowed buffers for later initialization. -/
theorem Calls.frame (certified : Calls model program p buffers heap before actions after final statuses) :
    ∀ q, Outside p buffers q → after q = heap q := by
  induction certified with
  | nil => exact fun _ _ => rfl
  | cons _ _ _ memory _ ih =>
    exact fun q outside => (ih q outside).trans (memory.2.2.2 q outside)

theorem Calls.readonly (certified : Calls model program p buffers heap before actions after final statuses) :
    CReadOnly.Preserves heap after := by
  induction certified with
  | nil => exact .refl _
  | cons called _ _ _ _ ih => exact called.readonly.trans ih

theorem Calls.stored (certified : Calls model program p buffers heap before actions after final statuses)
    (initial : Stored model heap p buffers before) : Stored model after p buffers final := by
  induction certified with
  | nil => exact initial
  | cons _ nextStored _ _ _ ih => exact ih nextStored

end Rumoca.FMI3.CSRun
end
