import RumocaFMI3.MENumericalRun
import RumocaFMI3.TerminationEnvironment

noncomputable section
namespace Rumoca.FMI3.MENumericalRun
open CTree CMemory StaticFactory

/-- Initial storage supplies all later numerical and recovery calls, including
every reset epoch, through termination and release with the original lease. -/
theorem initialize_release (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E),
      program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
      program.internal.definitions InitializationExit.signature.name =
        some (.tree (Runtime.function model InitializationExit.signature)) →
      MEEnvironment.Quiet model program → StaticReset.ExecutionContract program →
      Termination.ReleaseContract objects program tag →
      ∀ (heap : Heap) (slot : Fin objects.capacity) (owners : SlotOwners.State objects.capacity)
        (owner : Nat) (args : Initialization.Arguments) (seed : Binary64.Value)
        (addresses : String → Address) (buffer : Address) (actions : List Action)
        (final : MENumericalHistory.ReferenceState),
      let p := objects.instances.index slot.val
      args.Admissible → InitializationCalls.EntryStorage heap p →
      load heap (p.member "kind") = some (.integer 0) →
      heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite seed)⟩ →
      MENumericalHistory.CallerStorage heap p addresses buffer →
      ReferenceTrace (MENumericalHistory.ReferenceState.initial args seed) actions final →
      SlotOwners.Represents objects.flagsBlock heap owners → owners slot = some owner →
      load heap (p.member "slot") = some (.integer slot.val) →
      let entered := InitializationEntry.finalHeap heap p args
      let exited := InitializationCalls.exitedHeap heap p args .me
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling InitializationCalls.signature.name
          (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, entered⟩) ∧
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) entered .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, exited⟩) ∧
      ∃ after finalClock epochs,
        Calls program p addresses buffer exited actions
          (observations model (MENumericalHistory.ReferenceState.initial args seed) actions) after epochs ∧
        MENumericalHistory.Stored after p finalClock final addresses buffer ∧ Reset.Storage after p ∧
        CReadOnly.Preserves heap after ∧
        let terminated := LifecycleBodies.writeMode after p .terminated
        let released := replace terminated (AtomicSlots.address objects.flagsBlock slot) (CAtomicBoolean.cell false)
        (∀ behavior, (CCalls.Events.machine program).Behaves
          (.calling Termination.signature.name [.pointer (some p)] after .done) behavior ↔
          behavior = .terminates [] ⟨.integer 0, terminated⟩) ∧
        SlotOwners.release owners slot owner = some (SlotOwners.update owners slot none) ∧
        SlotOwners.Represents objects.flagsBlock released (SlotOwners.update owners slot none) ∧
        (∀ behavior, (CCalls.Events.machine program).Behaves
          (.calling StaticRelease.function.signature.name [.pointer (some p)] terminated .done) behavior ↔
          behavior = .terminates [tag (.write (AtomicSlots.address objects.flagsBlock slot) false)] ⟨.void, released⟩) ∧
        (∀ q, Outside p addresses buffer q → q ≠ AtomicSlots.address objects.flagsBlock slot → released q = heap q) := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program tag enterDefined exitDefined quiet reset finish heap slot owners owner args seed addresses buffer actions final
  let p := objects.instances.index slot.val
  dsimp only
  intro admissible storage kind stateCell outputs admitted represented owned metadata
  obtain ⟨enteredCall, exitedCall⟩ := InitializationEnvironment.calls header objects literals model
    program heap p args .me enterDefined exitDefined admissible storage kind
  have initialStored := MENumericalHistory.initialized_stored heap p args seed addresses buffer admissible kind stateCell outputs
  have initialReset := MENumericalHistory.initialized_reset_storage heap p args seed stateCell
  obtain ⟨after, finalClock, epochs, called, finalStored, finalReset, readonly, atomic, frame⟩ :=
    trace header objects literals model program quiet reset enterDefined exitDefined
      _ p _ _ final addresses buffer actions initialStored initialReset admitted
  have representedAfter := SlotOwners.ordinary_preserves
    (StaticInitialization.exited_owners objects heap slot args .me owners represented) atomic
  have slotOutside : Outside p addresses buffer (p.member "slot") :=
    ⟨initialStored.slot_outside, by simp, by simp⟩
  have metadataAfter : load after (p.member "slot") = some (.integer slot.val) := by
    simpa only [load, frame _ slotOutside] using
      ((StaticInitialization.exited_metadata heap p args .me).trans metadata)
  obtain ⟨terminated, discharged, releasedOwners, releasedFrame, freed⟩ :=
    finish after slot owners owner .me final.control.mode finalStored.control.kind finalStored.control.mode
      (admitted.live (Or.inl rfl)).terminate representedAfter owned metadataAfter
  have readonlyEnter := CCalls.Events.termination_preserves ((enteredCall _).mpr rfl)
  have readonlyExit := CCalls.Events.termination_preserves ((exitedCall _).mpr rfl)
  refine ⟨enteredCall, exitedCall, after, finalClock, epochs, called, finalStored, finalReset,
    readonlyEnter.trans (readonlyExit.trans readonly), terminated, discharged, releasedOwners, freed, ?_⟩
  intro q outside flag
  have parts := outside
  obtain ⟨⟨⟨time, mode, event, minimum, completed, _⟩, _, _⟩, stop, stopDefined⟩ := parts
  exact ((releasedFrame q mode flag).trans (frame q outside)).trans
    (InitializationCalls.exited_frame heap p q args .me time minimum event completed stop stopDefined mode)

end Rumoca.FMI3.MENumericalRun
end
