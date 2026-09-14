import RumocaFMI3.CSRunCompleted

noncomputable section
namespace Rumoca.FMI3.CSRun
open CMemory StaticFactory CCalls.Events

variable [CInterface] {program : Program Invocation}

theorem ActionContract.realizes (certified : ActionContract program p heap action status returns blocked)
    (outcome : returns events after) : Performed program p heap action status events after := by
  cases certified with
  | silent executed =>
    obtain ⟨rfl, rfl⟩ := outcome
    exact executed.performed
  | logged name effect args called =>
    obtain ⟨rfl, value, returned⟩ := outcome
    exact .step ((called _).mpr (Or.inl ⟨value, after, returned, rfl⟩))

/-- Returning alternatives are exactly the raw C executions; even restart
success follows from the contract rather than the raw relation's definition. -/
theorem ActionContract.performed_iff (certified : ActionContract program p heap action status returns blocked) :
    Performed program p heap action observed events after ↔ observed = status ∧ returns events after := by
  constructor
  · exact certified.performed_status
  · rintro ⟨rfl, outcome⟩
    exact certified.realizes outcome

theorem ActionContract.faulted_iff (certified : ActionContract program p heap action status returns blocked) :
    Faulted program p heap action ↔ blocked := by
  constructor
  · intro faulted
    cases faulted with
    | step called =>
      rcases (certified.step_behaviors _).mp called with ⟨_, _, _, impossible⟩ | ⟨blocked, _⟩
      · cases impossible
      · exact blocked
    | reset called =>
      cases certified with
      | silent executed =>
        cases executed with
        | restart reset _ _ => cases (reset _).mp called
    | enter resetCall enterCall =>
      cases certified with
      | silent executed =>
        cases executed with
        | restart reset enter _ =>
          cases (reset _).mp resetCall
          cases (enter _).mp enterCall
    | exit resetCall enterCall exitCall =>
      cases certified with
      | silent executed =>
        cases executed with
        | restart reset enter leave =>
          cases (reset _).mp resetCall
          cases (enter _).mp enterCall
          cases (leave _).mp exitCall
  · intro blocked
    cases certified with
    | silent _ => exact False.elim blocked
    | logged _ _ _ called => exact .step ((called _).mpr (Or.inr ⟨blocked, rfl⟩))

theorem ActionContract.progress (certified : ActionContract program p heap action status returns blocked) :
    (∃ events after, returns events after ∧ Performed program p heap action status events after) ∨
      (blocked ∧ Faulted program p heap action) := by
  classical
  have alternative : (∃ events after, returns events after) ∨ blocked := by
    cases certified with
    | silent _ => exact Or.inl ⟨[], _, rfl, rfl⟩
    | logged name effect args called =>
      rename_i callbackHeap request outputs
      by_cases returning : ∃ value after, effect.execute args callbackHeap value after
      · obtain ⟨value, after, returned⟩ := returning
        exact Or.inl ⟨_, after, rfl, value, returned⟩
      · exact Or.inr (fun value after returned => returning ⟨value, after, returned⟩)
  rcases alternative with ⟨events, after, outcome⟩ | blocked
  · exact Or.inl ⟨events, after, outcome, certified.realizes outcome⟩
  · exact Or.inr ⟨blocked, certified.faulted_iff.mpr blocked⟩

/-- Every finite certified script has a completed execution or a prefix
ending at a real blocked call. No callback totality assumption is needed. -/
theorem LoggedTrace.progress
    (certified : LoggedTrace objects logger owners model program p buffers heap before actions final statuses) :
    (∃ events after, Completed program p heap actions statuses events after) ∨ Stopped program p heap actions := by
  induction certified with
  | nil => exact Or.inl ⟨[], _, .nil⟩
  | cons called _ _ ih =>
    rcases called.progress with ⟨events, middle, outcome, performed⟩ | ⟨_, faulted⟩
    · rcases ih events middle outcome with ⟨later, after, completed⟩ | stopped
      · exact Or.inl ⟨_, after, .cons performed completed⟩
      · exact Or.inr (.later performed stopped)
    · exact Or.inr (.here faulted)

end Rumoca.FMI3.CSRun
end
