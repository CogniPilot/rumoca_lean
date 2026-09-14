import RumocaFMI3.MEMixedRun

noncomputable section
namespace Rumoca.FMI3
open CMemory CCalls.Events

namespace MENumericalRun

/-- A raw blocked numerical/restart action. Completed calls inside a restart
retain arbitrary returned values and actual intermediate heaps. -/
inductive Faulted [CInterface] (program : Program E) (p : Address)
    (addresses : String → Address) (buffer : Address) : Heap → Action → Prop where
  | numerical : action.Prepares heap ready buffer →
      (machine program).Behaves (.calling (action.call p addresses buffer).1
        (action.call p addresses buffer).2 ready .done) (.wrong []) →
      Faulted program p addresses buffer heap (.numerical action)
  | reset : (machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] heap .done) (.wrong []) →
      Faulted program p addresses buffer heap (.restart args)
  | enter : (machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] heap .done)
        (.terminates events ⟨status, resetHeap⟩) →
      (machine program).Behaves (.calling InitializationCalls.signature.name
        (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) resetHeap .done) (.wrong []) →
      Faulted program p addresses buffer heap (.restart args)
  | exit : (machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] heap .done)
        (.terminates resetEvents ⟨resetStatus, resetHeap⟩) →
      (machine program).Behaves (.calling InitializationCalls.signature.name
        (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) resetHeap .done)
        (.terminates enterEvents ⟨enterStatus, enteredHeap⟩) →
      (machine program).Behaves (.calling InitializationExit.signature.name
        (InitializationExit.arguments (some p)) enteredHeap .done) (.wrong []) →
      Faulted program p addresses buffer heap (.restart args)

theorem Calls.not_faulted [CInterface] {program : Program E}
    (certified : Calls program p addresses buffer heap [action] values after epochs) :
    ¬ Faulted program p addresses buffer heap action := by
  intro actual
  cases actual with
  | numerical prepared blocked =>
    cases certified with
    | numerical called _ =>
      cases called with
      | cons preparation behavior _ _ _ =>
        cases MENumericalHistory.Action.Prepares.unique preparation prepared
        cases (behavior _).mp blocked
  | reset blocked =>
    cases certified with
    | restart reset _ _ _ => cases (reset _).mp blocked
  | enter resetCall blocked =>
    cases certified with
    | restart reset enter _ _ =>
      cases (reset _).mp resetCall
      cases (enter _).mp blocked
  | exit resetCall enterCall blocked =>
    cases certified with
    | restart reset enter leave _ =>
      cases (reset _).mp resetCall
      cases (enter _).mp enterCall
      cases (leave _).mp blocked

end MENumericalRun
namespace MEMixedRun

inductive Faulted [CInterface] (program : Program Invocation) (p : Address)
    (addresses : String → Address) (buffer : Address) : Heap → Action → Prop where
  | run : MENumericalRun.Faulted program p addresses buffer heap action →
      Faulted program p addresses buffer heap (.run action)
  | reject : MEFailure.Prepares input heap ready buffer →
      (machine program).Behaves (.calling (request.call p).1 (request.call p).2 ready .done) (.wrong []) →
      Faulted program p addresses buffer heap (.reject request input)

inductive Stopped [CInterface] (program : Program Invocation) (p : Address)
    (addresses : String → Address) (buffer : Address) : Heap → List Action → Prop where
  | here : Faulted program p addresses buffer heap action →
      Stopped program p addresses buffer heap (action :: rest)
  | later : Performed program p addresses buffer heap action observed middle epochs →
      Stopped program p addresses buffer middle rest →
      Stopped program p addresses buffer heap (action :: rest)

variable [CInterface] {program : Program Invocation}

theorem ActionContract.performed_iff
    (certified : ActionContract program p addresses buffer heap action returns blocked) :
    Performed program p addresses buffer heap action observed after epochs ↔ returns observed after epochs :=
  ⟨certified.returned, certified.realizes⟩

theorem ActionContract.faulted_iff
    (certified : ActionContract program p addresses buffer heap action returns blocked) :
    Faulted program p addresses buffer heap action ↔ blocked := by
  constructor
  · intro actual
    cases actual with
    | run faulted =>
      cases certified with
      | run called => exact False.elim (called.not_faulted faulted)
    | reject prepared faulted =>
      cases certified with
      | quiet preparation called =>
        cases MEFailure.Prepares.unique preparation prepared
        cases (called _).mp faulted
      | logged _ _ _ preparation called =>
        cases MEFailure.Prepares.unique preparation prepared
        rcases (called _).mp faulted with ⟨_, _, _, impossible⟩ | ⟨blocked, _⟩
        · cases impossible
        · exact blocked
  · intro blocked
    cases certified with
    | run _ | quiet _ _ => exact False.elim blocked
    | logged _ _ _ prepared called => exact .reject prepared ((called _).mpr (Or.inr ⟨blocked, rfl⟩))

theorem ActionContract.faulted_rejection
    (certified : ActionContract program p addresses buffer heap action returns blocked)
    (actual : Faulted program p addresses buffer heap action) : ∃ request input, action = .reject request input := by
  have blocked := certified.faulted_iff.mp actual
  cases certified with
  | run _ | quiet _ _ => exact False.elim blocked
  | logged _ _ _ _ _ => exact ⟨_, _, rfl⟩

/-- Every modeled returning or blocked alternative is derived, with no
callback totality or deterministic-callback premise. -/
theorem ActionContract.progress
    (certified : ActionContract program p addresses buffer heap action returns blocked) :
    (∃ observed after epochs, returns observed after epochs ∧ Performed program p addresses buffer heap action observed after epochs) ∨
    (blocked ∧ Faulted program p addresses buffer heap action) := by
  classical
  have alternative : (∃ observed after epochs, returns observed after epochs) ∨ blocked := by
    cases certified with
    | run _ => exact Or.inl ⟨_, _, _, rfl, rfl, rfl⟩
    | quiet _ _ => exact Or.inl ⟨_, _, _, rfl, rfl, rfl⟩
    | logged name effect args prepared called =>
      rename_i input heap ready callbackHeap request
      by_cases returning : ∃ value after, effect.execute args callbackHeap value after
      · obtain ⟨value, after, returned⟩ := returning
        exact Or.inl ⟨_, after, [], rfl, rfl, value, returned⟩
      · exact Or.inr (fun value after returned => returning ⟨value, after, returned⟩)
  rcases alternative with ⟨observed, after, epochs, outcome⟩ | blocked
  · exact Or.inl ⟨observed, after, epochs, outcome, certified.realizes outcome⟩
  · exact Or.inr ⟨blocked, certified.faulted_iff.mpr blocked⟩

theorem Trace.progress {model : Solve.FMI3Model source} {objects : StaticFactory.Objects}
    {owners : SlotOwners.State objects.capacity} {config : Configuration}
    (certified : Trace model objects owners config program p addresses buffer heap reference clock actions final finalClock) :
    (∃ observed after epochs, Completed program p addresses buffer heap actions observed after epochs) ∨
    Stopped program p addresses buffer heap actions := by
  induction certified with
  | nil => exact Or.inl ⟨[], _, [], .nil⟩
  | cons called _ _ ih =>
    rcases called.progress with ⟨observed, middle, epochs, outcome, performed⟩ | ⟨_, faulted⟩
    · rcases ih observed middle epochs outcome with ⟨following, after, checkpoints, completed⟩ | stopped
      · exact Or.inl ⟨_, after, _, .cons performed completed⟩
      · exact Or.inr (.later performed stopped)
    · exact Or.inr (.here faulted)

end MEMixedRun
end Rumoca.FMI3
end
