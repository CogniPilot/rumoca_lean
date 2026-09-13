import RumocaFMI3.MEInitialization
import RumocaFMI3.MERelease
import RumocaFMI3.StaticInitialization

noncomputable section
namespace Rumoca.FMI3.MEHistory
open CTree CMemory StaticFactory

theorem Buffers.storage_preserved (buffers : Buffers before addresses)
    (preserved : CStorage.Preserves before after) : Buffers after addresses := by
  intro layout member
  obtain ⟨old, found⟩ := buffers layout member
  exact preserved.cell found

/-- The same program executes initialization, controls, termination and
release. Initialization supplies every later invariant and the original lease
is carried through the trace, with no post-initialization execution premise. -/
theorem initialize_release [interface : CInterface] (objects : Objects)
    (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (initialization : InitializationCalls.QuietExecutionContract program)
    (finish : ReleaseContract objects program tag)
    (heap : Heap) (slot : Fin objects.capacity) (owners : SlotOwners.State objects.capacity)
    (owner : Nat) (args : Initialization.Arguments) (model : ModelExchange.State)
    (addresses : String → Address) (actions : List Action) (final : ReferenceState)
    (admissible : args.Admissible)
    (storage : InitializationCalls.EntryStorage heap (objects.instances.index slot.val))
    (kind : load heap ((objects.instances.index slot.val).member "kind") = some (.integer 0))
    (state : StateProofs.Represents heap (objects.instances.index slot.val) model)
    (buffers : Buffers heap addresses) (outside : Buffers.Outside objects.instances addresses)
    (admitted : ReferenceTrace (ReferenceState.initial args.start args.stopTime) actions final)
    (represented : SlotOwners.Represents objects.flagsBlock heap owners) (owned : owners slot = some owner)
    (metadata : load heap ((objects.instances.index slot.val).member "slot") = some (.integer slot.val)) :
    let p := objects.instances.index slot.val
    let entered := InitializationEntry.finalHeap heap p args
    let exited := InitializationCalls.exitedHeap heap p args .me
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling InitializationCalls.signature.name
        (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, entered⟩) ∧
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) entered .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, exited⟩) ∧
    ∃ after finalClock,
      Calls program p addresses exited actions after ∧ Stored after p finalClock final model addresses ∧
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
      (∀ query, Outside p addresses query → query ≠ p.member "stop" →
        query ≠ p.member "stopDefined" → query ≠ AtomicSlots.address objects.flagsBlock slot →
        released query = heap query) := by
  let p := objects.instances.index slot.val
  have ready := initialized_stored heap p args model addresses admissible kind state buffers outside
  obtain ⟨after, finalClock, called, storedAfter, terminated, discharged, ownersAfter, freed, framed⟩ :=
    finish (InitializationCalls.exitedHeap heap p args .me) slot owners owner (Time.Clock.initial args.start)
      (ReferenceState.initial args.start args.stopTime) final model addresses actions ready (Or.inl rfl)
      admitted (StaticInitialization.exited_owners objects heap slot args .me owners represented) owned
      ((StaticInitialization.exited_metadata heap p args .me).trans metadata)
  refine ⟨initialization.enter heap p args .me admissible storage kind,
    initialization.exit (InitializationEntry.finalHeap heap p args) p .me
      ((InitializationCalls.entered_kind heap p args).trans kind) (InitializationCalls.entered_mode heap p args),
    after, finalClock, called, storedAfter, terminated, discharged, ownersAfter, freed, ?_⟩
  intro query separateFields stop stopDefined flag
  have decomposed := separateFields
  obtain ⟨time, mode, event, minimum, completed, _⟩ := decomposed
  exact (framed query separateFields flag).trans
    (InitializationCalls.exited_frame heap p query args .me time minimum event completed stop stopDefined mode)

end Rumoca.FMI3.MEHistory
