import RumocaFMI3.MEFailureMemory
import RumocaFMI3.MENumericalRun

noncomputable section
namespace Rumoca.FMI3.MEFailure
open CTree CMemory StaticFactory

/-- A recovery certificate exposes all three calls through the existing raw
history semantics, and supplies the storage required by further ME operations. -/
structure Recovery [CInterface] (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
    (args : Initialization.Arguments) (addresses : String → Address) (buffer : Address) : Prop where
  calls : MENumericalRun.Calls program p addresses buffer heap [.restart args] [none, none, none]
    (MENumericalHistory.restarted heap p args) [(args, MENumericalHistory.restarted heap p args)]
  stored : MENumericalHistory.Stored (MENumericalHistory.restarted heap p args) p (Time.Clock.initial args.start)
    (MENumericalHistory.ReferenceState.restart args) addresses buffer
  resetStorage : Reset.Storage (MENumericalHistory.restarted heap p args) p
  readonly : CReadOnly.Preserves heap (MENumericalHistory.restarted heap p args)
  atomic : CAtomicBoolean.Preserves heap (MENumericalHistory.restarted heap p args)
  frame : ∀ q, ¬ p.InRecord q → MENumericalHistory.restarted heap p args q = heap q

theorem Recovery.correct (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E),
      StaticReset.ExecutionContract program →
      program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
      program.internal.definitions InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) →
      ∀ (heap : Heap) (p : Address) (clock : Time.Clock) (reference : MENumericalHistory.ReferenceState)
        (addresses : String → Address) (buffer : Address) (args : Initialization.Arguments),
      MENumericalHistory.Stored heap p clock reference addresses buffer → Reset.Storage heap p → args.Admissible →
      Recovery program heap p args addresses buffer := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program reset enterDefined exitDefined heap p clock reference addresses buffer args stored storage admissible
  have resetCall := reset.successful heap p .me reference.control.mode storage stored.control.kind stored.mode_loaded
  obtain ⟨enterCall, exitCall⟩ := InitializationEnvironment.calls header objects literals model program
    (Reset.finalHeap heap p) p args .me enterDefined exitDefined admissible (StaticReset.entry_storage heap p)
    ((StaticReset.kind_value heap p).trans stored.control.kind)
  exact ⟨.restart resetCall enterCall exitCall .nil, stored.restart args admissible,
    MENumericalHistory.initialized_reset_storage (Reset.finalHeap heap p) p args Binary64.positiveZero
      (MENumericalHistory.reset_state_cell heap p),
    (CCalls.Events.termination_preserves ((resetCall _).mpr rfl)).trans
      ((CCalls.Events.termination_preserves ((enterCall _).mpr rfl)).trans
        (CCalls.Events.termination_preserves ((exitCall _).mpr rfl))),
    MENumericalHistory.restart_atomic storage args,
    fun q outside => StaticReset.restarted_frame heap p q args .me outside⟩

theorem Recovery.determines [CInterface] {program : CCalls.Events.Program E}
    (certified : Recovery program heap p args addresses buffer)
    (executed : MENumericalRun.Executed program p addresses buffer heap [.restart args] observed after epochs) :
    observed = ([none, none, none].map MENumericalHistory.Observation.ok) ∧
    after = MENumericalHistory.restarted heap p args ∧ epochs = [(args, after)] := by
  obtain ⟨values, memory, checkpoints⟩ := certified.calls.determines executed
  exact ⟨values, memory, by rw [memory]; exact checkpoints⟩

theorem Recovery.owners [CInterface] {owners : SlotOwners.State capacity} {program : CCalls.Events.Program E}
    (certified : Recovery program heap p args addresses buffer)
    (represented : SlotOwners.Represents flags heap owners) :
    SlotOwners.Represents flags (MENumericalHistory.restarted heap p args) owners :=
  SlotOwners.ordinary_preserves represented certified.atomic

end Rumoca.FMI3.MEFailure
end
