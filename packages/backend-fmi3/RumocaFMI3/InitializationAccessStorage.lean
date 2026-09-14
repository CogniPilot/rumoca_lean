import RumocaFMI3.InitializationAccess
import RumocaFMI3.CSCreationStorage
import RumocaFMI3.StaticInitialization
import RumocaFMI3.CSInitialization
import RumocaFMI3.LifecycleRelease

noncomputable section
namespace Rumoca.FMI3
open CMemory Float64Access StaticFactory

theorem InstanceInitialization.Initialized.access_instance
    (initialized : InstanceInitialization.Initialized heap p kind environment logger logging)
    (initial : Binary64.Value) (loaded : load heap (StateProofs.stateAddress p) = some (.finite initial)) :
    Instance heap p kind .instantiated ⟨initial⟩ Binary64.positiveZero := by
  refine ⟨initialized.kindValue, (StaticInitialization.entry_storage initialized).mode,
    initialized.state_cell initial loaded, ?_⟩
  simp [load, initialized.clock.time, HistoryProofs.cell, Time.Clock.initial, convert, Value.finite]

theorem Float64Buffers.Layout.Separate.at_index {buffers : Float64Buffers.Layout}
    (separate : buffers.Separate p) (index : Nat) :
    buffers.Separate (p.index index) :=
  ⟨separate.references, separate.values, separate.eachOther⟩

namespace InitializationAccess
variable [interface : CInterface] {program : CCalls.Events.Program E}

theorem Certificate.owners
    {owners : SlotOwners.State capacity}
    (certified : Certificate model program p buffers args kind state time heap before during beforeEntry atExit)
    (represented : SlotOwners.Represents block heap owners) :
    SlotOwners.Represents block (InitializationBodies.exitHeap atExit p kind) owners :=
  SlotOwners.ordinary_preserves represented certified.atomic

theorem Certificate.metadata
    (certified : Certificate model program p buffers args kind state time heap before during beforeEntry atExit) :
    load (InitializationBodies.exitHeap atExit p kind) (p.member "slot") = load heap (p.member "slot") := by
  have same := (InitializationBodies.exit_frame atExit p (p.member "slot") kind (by simp)).trans
    ((certified.atExitFields "slot").trans
      ((InitializationEntry.frame beforeEntry p (p.member "slot") args
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans
        (certified.beforeFields "slot")))
  simp only [load, same]

/-- The executable CS seed is the value after all initialization writes.
Original step-output storage survives even if those buffers were used by
earlier accesses. This does not assume a contiguous entry/exit sequence. -/
theorem Certificate.cs_storage
    (certified : Certificate model program p buffers args .cs state time heap before during beforeEntry atExit)
    (admissible : args.Admissible) (outputs : StepArguments.Storage heap p stepBuffers) :
    CSHistory.Stored model.solve (finalState during (finalState before state)).x
      (InitializationBodies.exitHeap atExit p .cs) p stepBuffers ⟨args.start, 0⟩ args.stopTime := by
  have fields (name : String) (notMode : name ≠ "mode") :
      load (InitializationBodies.exitHeap atExit p .cs) (p.member name) =
        load (InitializationEntry.finalHeap beforeEntry p args) (p.member name) := by
    simp only [load, InitializationBodies.exit_frame atExit p (p.member name) .cs
      (by simpa using notMode), certified.atExitFields]
  refine ⟨certified.instanceStored.kind, certified.instanceStored.mode_loaded,
    certified.clockStored.time, certified.instanceStored.state, ?_, ?_, outputs.storage_preserved certified.storage⟩
  · rw [fields "stopDefined" (by decide)]
    simpa only [Initialization.stopTime_defined args admissible] using (InitializationEntry.stop beforeEntry p args).2
  · intro limit selected
    rw [fields "stop" (by decide)]
    simpa only [Value.finite, Initialization.stopTime_bits args admissible limit selected]
      using (InitializationEntry.stop beforeEntry p args).1

theorem Certificate.release (objects : Objects) (tag : CAtomicBoolean.Calls.Event → E)
    (slot : Fin objects.capacity) {owners : SlotOwners.State objects.capacity}
    (certified : Certificate model program (objects.instances.index slot.val) buffers args kind state time
      heap before during beforeEntry atExit)
    (finish : Termination.ReleaseContract objects program tag) (release : StaticRelease.Bindings program tag)
    (flags : interface.constants "rumoca_instance_flags" = some (.pointer (some ⟨objects.flagsBlock, [], 0⟩)))
    (represented : SlotOwners.Represents objects.flagsBlock heap owners) (owned : owners slot = some owner)
    (metadata : load heap ((objects.instances.index slot.val).member "slot") = some (.integer slot.val)) :
    LifecycleRelease.Released objects program tag (InitializationBodies.exitHeap atExit (objects.instances.index slot.val) kind)
      slot owners owner kind (nextMode .exitInitialization kind .initialization) := by
  exact LifecycleRelease.finish_correct objects program tag finish release flags _ slot kind _ owners owner
    certified.instanceStored.kind certified.instanceStored.mode
    (by cases kind <;> exact Or.inl (by simp [Reference.Allowed, me_initialization, cs_initialization]))
    (certified.owners represented) owned
    (certified.metadata.trans metadata)

end InitializationAccess
end Rumoca.FMI3
end
