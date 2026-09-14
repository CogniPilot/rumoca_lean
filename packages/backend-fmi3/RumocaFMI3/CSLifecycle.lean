import RumocaFMI3.CSInitialization
import RumocaFMI3.CSRelease
import RumocaFMI3.InitializationEnvironment

noncomputable section
namespace Rumoca.FMI3.CSHistory
open CTree CMemory StaticFactory CCalls

/-- The complete successful initialization/CS/termination/release sequence
is derived from original storage and ownership. Later callers obtain their
premises from the preceding calls, with no assumed post-simulation lease. -/
theorem initialize_release (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (signatures : List Signature)
    (seed : Binary64.Value) (slot : Fin objects.capacity) (buffers : StepEntry.Buffers)
    (args : Initialization.Arguments)
    (contracts : ∀ (reference : ReferenceState) (request : Request), StepCalls.AcceptedContract
      (request.query header (objects.instances.index slot.val) buffers reference args.stopTime)
      objects literals model signatures) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
      (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
      program.internal = LiteralPreparation.program model signatures →
      program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
      program.externals "floor" = some (CMathCalls.floorExternal rfl) →
      program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
      program.internal.definitions InitializationExit.signature.name =
        some (.tree (Runtime.function model InitializationExit.signature)) →
      Termination.ReleaseContract objects program tag →
      ∀ (heap : Heap) (requests : List Request) (final : ReferenceState)
        (owners : SlotOwners.State objects.capacity) (owner : Nat),
      let p := objects.instances.index slot.val
      args.Admissible → InitializationCalls.EntryStorage heap p →
      load heap (p.member "kind") = some (.integer 1) →
      heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite seed)⟩ →
      StepArguments.Storage heap p buffers → ReferenceTrace args.stopTime ⟨args.start, 0⟩ requests final →
      SlotOwners.Represents objects.flagsBlock heap owners → owners slot = some owner →
      load heap (p.member "slot") = some (.integer slot.val) →
      let entered := InitializationEntry.finalHeap heap p args
      let exited := InitializationCalls.exitedHeap heap p args .cs
      (∀ behavior, (Events.machine program).Behaves
        (.calling InitializationCalls.signature.name
          (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, entered⟩) ∧
      (∀ behavior, (Events.machine program).Behaves
        (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) entered .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, exited⟩) ∧
      ∃ after, Calls program p buffers exited ⟨args.start, 0⟩ requests after final ∧
        Stored model.solve seed after p buffers final args.stopTime ∧
        let terminated := LifecycleBodies.writeMode after p .terminated
        let released := replace terminated (AtomicSlots.address objects.flagsBlock slot) (CAtomicBoolean.cell false)
        (∀ behavior, (Events.machine program).Behaves
          (.calling Termination.signature.name [.pointer (some p)] after .done) behavior ↔
          behavior = .terminates [] ⟨.integer 0, terminated⟩) ∧
        SlotOwners.release owners slot owner = some (SlotOwners.update owners slot none) ∧
        SlotOwners.Represents objects.flagsBlock released (SlotOwners.update owners slot none) ∧
        (∀ behavior, (Events.machine program).Behaves
          (.calling StaticRelease.function.signature.name [.pointer (some p)] terminated .done) behavior ↔
          behavior = .terminates [tag (.write (AtomicSlots.address objects.flagsBlock slot) false)] ⟨.void, released⟩) ∧
        (∀ query, Outside p buffers query → query ≠ p.member "mode" →
          query ≠ p.member "timeMin" → query ≠ p.member "eventTime" → query ≠ p.member "lastCompleted" →
          query ≠ p.member "stop" → query ≠ p.member "stopDefined" →
          query ≠ AtomicSlots.address objects.flagsBlock slot → released query = heap query) := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program tag range actual rounding floorBound enterDefined exitDefined finish
    heap requests final owners owner
  let p := objects.instances.index slot.val
  dsimp only
  intro admissible storage kind state outputs admitted represented owned metadata
  obtain ⟨entered, exited⟩ := InitializationEnvironment.calls header objects literals model
    program heap p args .cs enterDefined exitDefined admissible storage kind
  have initialStored := initialized_stored model.solve seed heap p args buffers admissible kind state outputs
  obtain ⟨after, calls, finalStored, atomic, frame⟩ := trace_atomic_frame header objects literals
    model signatures seed p buffers args.stopTime contracts program range actual rounding floorBound
    (InitializationCalls.exitedHeap heap p args .cs) ⟨args.start, 0⟩ final requests initialStored admitted
  have mode : InitializationCalls.exitedHeap heap p args .cs (p.member "mode") =
      some ⟨.int32, true, some (.integer 4)⟩ := by
    simp [InitializationCalls.exitedHeap, InitializationBodies.exitHeap, cs_initialization, Mode.code]
  obtain ⟨_, terminated, discharged, ownersAfter, freed, releasedFrame⟩ := release_history
    objects program tag finish model.solve seed (InitializationCalls.exitedHeap heap p args .cs) after
    slot buffers ⟨args.start, 0⟩ final args.stopTime requests owners owner initialStored mode calls finalStored atomic frame
    (StaticInitialization.exited_owners objects heap slot args .cs owners represented) owned
    ((StaticInitialization.exited_metadata heap p args .cs).trans metadata)
  refine ⟨entered, exited, after, calls, finalStored, terminated, discharged, ownersAfter, freed, ?_⟩
  intro query outside outsideMode minimum event completed stop stopDefined flag
  exact (releasedFrame query outside outsideMode flag).trans
    (InitializationCalls.exited_frame heap p query args .cs outside.2.1 minimum event completed stop stopDefined outsideMode)

end Rumoca.FMI3.CSHistory
end
