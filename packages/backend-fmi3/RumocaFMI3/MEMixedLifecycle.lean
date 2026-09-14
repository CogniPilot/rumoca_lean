import RumocaFMI3.MEMixedExecution
import RumocaFMI3.LifecycleRelease
import RumocaFMI3.InstanceInitialization
import RumocaFMI3.FactoryArguments

noncomputable section
namespace Rumoca.FMI3.MEMixedRun
open CTree CMemory CBody StaticFactory CCalls.Events

theorem Action.can_finish (action : Action)
    (ready : LifecycleRelease.CanFinish .me reference.control.mode) :
    LifecycleRelease.CanFinish .me (action.next reference).control.mode := by
  cases action with
  | reject _ _ => exact Or.inr rfl
  | run command =>
    cases command with
    | restart _ => exact Or.inl (by simp [Action.next, MENumericalHistory.ReferenceState.restart,
        MENumericalHistory.ReferenceState.initial, MEHistory.ReferenceState.initial, Reference.Allowed])
    | numerical numerical =>
      cases numerical with
      | setState _ | getState | derivative => exact ready
      | control control =>
        cases control with
        | setTime _ | updateDiscrete | completed _ => exact ready
        | enter transition => cases transition <;> exact Or.inl (by simp [Action.next,
            MENumericalHistory.Action.next, MEHistory.Action.next, EventEntry.Entry.after,
            EventEntry.afterHistory, Reference.Allowed])

theorem ReferenceTrace.can_finish (trace : ReferenceTrace buffer reference clock actions final finalClock)
    (ready : LifecycleRelease.CanFinish .me reference.control.mode) :
    LifecycleRelease.CanFinish .me final.control.mode := by
  induction trace with
  | nil => exact ready
  | cons _ _ ih => exact ih (Action.can_finish _ ready)

/-- The history configuration comes from the original instantiation arguments,
before any initialized heap or future callback outcome is supplied. -/
def Configuration.Matches [CInterface] (config : Configuration) (args : FactoryArguments.Raw) : Prop :=
  match config with
  | .quiet logger logging => args.logger = logger ∧ args.logging = logging
  | .logged logger environment _ _ => args.logger = some logger ∧ args.logging = true ∧ args.environment = environment

theorem Configuration.created [CInterface] {config : Configuration}
    (matching : config.Matches args)
    (initialized : InstanceInitialization.Initialized heap p .me args.environment args.logger args.logging) :
    config.Stored heap p := by
  cases config with
  | quiet logger logging => exact ⟨by simpa only [matching.1] using initialized.loggerValue,
      by simpa only [matching.2] using initialized.loggingValue⟩
  | logged logger environment name effect =>
    exact ⟨by simpa only [matching.1] using initialized.loggerValue,
      by simpa only [matching.2.1, boolean] using initialized.loggingValue,
      by simpa only [matching.2.2] using initialized.environmentValue⟩

theorem Configuration.initialized [CInterface] {config : Configuration}
    (stored : config.Stored heap p) (args : Initialization.Arguments) :
    config.Stored (InitializationCalls.exitedHeap heap p args .me) p := by
  apply stored.framed
  intro name member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  apply InitializationCalls.exited_frame <;> rcases member with rfl | rfl | rfl <;> simp

/-- A completed history preserves the slot metadata needed by release,
including across every returning logger branch and reset epoch. -/
theorem Trace.slot [CInterface] {source : AST.Model} {program : Program Invocation} {model : Solve.FMI3Model source}
    {owners : SlotOwners.State objects.capacity} {config : Configuration}
    (certified : Trace model objects owners config program p addresses buffer heap reference clock actions final finalClock)
    (stored : MENumericalHistory.Stored heap p clock reference addresses buffer)
    (inPool : p.block = objects.instances.block)
    (completed : Completed program p addresses buffer heap actions observed after epochs) :
    load after (p.member "slot") = load heap (p.member "slot") := by
  obtain ⟨_, _, _, _, _, frame⟩ := certified.completed completed
  simp only [load, frame (p.member "slot") (Or.inl inPool) (configuration_outside stored "slot" (by simp))]

end Rumoca.FMI3.MEMixedRun
end
