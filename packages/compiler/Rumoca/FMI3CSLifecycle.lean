import Rumoca.FMI3CSRelease
import Rumoca.FMI3StaticLifecycle
import RumocaFMI3.FactoryEnvironment
import RumocaFMI3.CSCreationStorage

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CLiteral CStringMemory StaticFactory

/-- The actual source-bound CS factory, initialization, accepted numerical
history, termination and release share one program and heap. Available static
storage supplies every created/initialized-state and later ownership premise.
Mixed error/reset histories and concurrent calls remain separate obligations. -/
theorem adapter_create_cs_release (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (header : CFenv.Header) (instances flags : Nat) (separate : instances ≠ flags)
        (before : Heap) (firstBlock : Nat) (signed : Bool),
        let objects := StaticRuntime.objects instances flags separate
        let literals := pool.addresses firstBlock
        letI : CInterface := RuntimeEnvironment.interface header objects literals
        ∀ (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
          (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        Identity.Bindings program →
        program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag rfl) →
        program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
        program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
        program.externals "floor" = some (CMathCalls.floorExternal rfl) →
        ∀ (args : FactoryArguments.Raw) (heap : Heap),
        CReadOnly.Preserves (pool.install before firstBlock signed) heap →
        CreationStorage heap objects.instances objects.flags objects.capacity →
        ∀ (name supplied : Address) (nameBytes tokenBytes : List UInt8),
        FactoryEntry.unsupported args = false →
        args.name = some name → args.token = some supplied →
        Contents heap name nameBytes → Contents heap supplied tokenBytes →
        nameBytes.length < 2^64 →
        Identity.accepted nameBytes (content " \t\n\r\u000c\u000b") tokenBytes
          (token a.solve.prepareFMI3).toUTF8.data.toList = true →
        ∀ (owners : SlotOwners.State objects.capacity),
        SlotOwners.Represents objects.flagsBlock heap owners →
        (∃ slot, owners slot = none) →
        ∀ (owner : Nat) (initArgs : Initialization.Arguments) (buffers : StepEntry.Buffers)
          (requests : List CSHistory.Request) (final : CSHistory.ReferenceState),
        initArgs.Admissible → StepArguments.Storage heap objects.instances buffers →
        CSHistory.ReferenceTrace initArgs.stopTime ⟨initArgs.start, 0⟩ requests final →
        ∃ trace : List CAtomicBoolean.Calls.Event, ∃ slot : Fin objects.capacity,
        ∃ live after, ∃ initial : Binary64.Value,
          let p := objects.instances.index slot.val
          let entered := InitializationEntry.finalHeap live p initArgs
          let exited := InitializationCalls.exitedHeap live p initArgs .cs
          let trajectory := Initialization.trajectory (Binary64.value initArgs.start) (Binary64.value initial)
          let terminated := LifecycleBodies.writeMode after p .terminated
          let released := replace terminated (AtomicSlots.address objects.flagsBlock slot) (CAtomicBoolean.cell false)
          trace.length ≤ objects.capacity ∧
          SlotOwners.reserve owners slot owner = some (SlotOwners.update owners slot (some owner)) ∧
          Created live objects.instances objects.flagsBlock (SlotOwners.update owners slot (some owner))
            slot owner .cs args.environment args.logger args.logging ∧
          Binary64.value initial = (a.solve.initial.initial : ℝ) ∧
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling (FactoryArguments.signature .cs).name (FactoryArguments.arguments .cs args) heap .done) behavior ↔
            behavior = .terminates (trace.map tag) ⟨.pointer (some p), live⟩) ∧
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling InitializationCalls.signature.name
              (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite initArgs)) live .done) behavior ↔
            behavior = .terminates [] ⟨.integer 0, entered⟩) ∧
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) entered .done) behavior ↔
            behavior = .terminates [] ⟨.integer 0, exited⟩) ∧
          InitializationCalls.SourceInitialized a.parsed.ast exited p initArgs.start trajectory ∧
          (∀ candidate, InitializationCalls.SourceInitialized a.parsed.ast exited p initArgs.start candidate → candidate = trajectory) ∧
          CSHistory.Calls program p buffers exited ⟨initArgs.start, 0⟩ requests after final ∧
          CSHistory.Stored a.solve initial after p buffers final initArgs.stopTime ∧
          |Binary64.value (a.solve.run initial final.elapsed) - trajectory (Binary64.value final.time)| ≤
            (final.elapsed : ℝ) + |Binary64.value final.time - (Binary64.value initArgs.start + (final.elapsed : ℝ))| ∧
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling Termination.signature.name [.pointer (some p)] after .done) behavior ↔
            behavior = .terminates [] ⟨.integer 0, terminated⟩) ∧
          SlotOwners.release (SlotOwners.update owners slot (some owner)) slot owner = some owners ∧
          SlotOwners.Represents objects.flagsBlock released owners ∧
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling StaticRelease.function.signature.name [.pointer (some p)] terminated .done) behavior ↔
            behavior = .terminates [tag (.write (AtomicSlots.address objects.flagsBlock slot) false)] ⟨.void, released⟩) ∧
          (∀ query, ¬ p.InRecord query → query ≠ buffers.event → query ≠ buffers.terminate →
            query ≠ buffers.early → query ≠ buffers.last →
            query ≠ AtomicSlots.address objects.flagsBlock slot → released query = heap query) := by
  obtain ⟨signatures, unique, _, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, initialization, _, factories, runtime, termination, _, _, _, _, step⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E header instances flags separate before firstBlock signed
  let objects := StaticRuntime.objects instances flags separate
  let literals := pool.addresses firstBlock
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  dsimp only
  intro program tag range actual identity exchange write rounding floorBound args heap literalFrame ready
    name supplied nameBytes tokenBytes supported nameBound tokenBound nameStored tokenStored fits accepted
    owners represented available owner initArgs buffers requests final admissible outputStorage admitted
  obtain ⟨request⟩ := prepared_static_identity a signatures (factories.member .cs) made before firstBlock signed heap
    literalFrame .cs args name supplied nameBytes tokenBytes (Or.inr supported)
    nameBound tokenBound nameStored tokenStored fits accepted
  have reserveBindings : ReservationBindings program tag :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, exchange, by rw [actual]; exact StaticRuntime.reservation_bound _ signatures⟩
  obtain ⟨trace, slot, live, work, reserved, created, preserved, createdFrame, creation⟩ :=
    FactoryEnvironment.create_owned header objects literals program tag identity _ .cs args heap request
      (by rw [actual]; exact StaticRuntime.factory_bound _ signatures unique .cs (factories.member .cs))
      (by rw [actual]; exact StaticRuntime.identity_bound _ signatures) ready reserveBindings
      owners represented available owner
  let p := objects.instances.index slot.val
  have enterDefined : program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) := by
    rw [actual, ← InitializationCalls.function_eq a.solve.prepareFMI3]
    exact LiteralPreparation.function_bound _ signatures unique _ initialization.enterMember
  have exitDefined : program.internal.definitions InitializationExit.signature.name =
      some (.tree (Runtime.function a.solve.prepareFMI3 InitializationExit.signature)) := by
    rw [actual]
    exact LiteralPreparation.function_bound _ signatures unique _ initialization.exitMember
  have releaseBindings : StaticRelease.Bindings program tag :=
    ⟨by rw [actual]; exact runtime.release_defined, rfl, rfl, rfl, rfl, rfl, rfl, write⟩
  have terminateQuiet : Termination.QuietContract program := by
    apply TerminationEnvironment.quiet_correct header objects literals a.solve.prepareFMI3 program
    rw [actual]
    exact LiteralPreparation.function_bound _ signatures unique _ termination.member
  have finish := TerminationEnvironment.release_correct header objects literals program tag terminateQuiet releaseBindings
  obtain ⟨initial, loaded, agreement, _, _⟩ := created.source_default a (Binary64.value initArgs.start)
  have state := created.initialized.state_cell initial loaded
  have outputs := (outputStorage.storage_preserved preserved).at_index slot.val
  obtain ⟨entered, exited, after, calls, stored, terminated, discharged, ownersAfter, freed, framed⟩ :=
    CSHistory.initialize_release header objects literals a.solve.prepareFMI3 signatures initial slot buffers initArgs
      (fun reference request => ((step.prepared pool made).quiet
        (request.query header p buffers reference initArgs.stopTime) objects firstBlock).2)
      program tag range actual rounding floorBound enterDefined exitDefined finish
      live requests final (SlotOwners.update owners slot (some owner)) owner admissible
      (StaticInitialization.entry_storage created.initialized) created.initialized.kindValue state outputs admitted
      created.represented created.owned created.metadata
  have initialStored := CSHistory.initialized_stored a.solve initial live p initArgs buffers admissible
    created.initialized.kindValue state outputs
  have initialized := InitializationCalls.exited_source_initialized a.solve.prepareFMI3 live p initArgs .cs ⟨initial⟩ loaded
  have uniqueInitial := InitializationBodies.exit_model (InitializationEntry.model loaded initArgs) .cs
  have restored := SlotOwners.release_reserved_restore reserved
  rw [restored] at discharged ownersAfter
  refine ⟨trace, slot, live, after, initial, work, reserved, created, agreement,
    creation, entered, exited, initialized,
    fun _ given => InitializationCalls.source_initialized_unique given uniqueInitial,
    calls, stored, CSHistory.source_error a.solve initial initArgs.start
      (InitializationCalls.exitedHeap live p initArgs .cs) p buffers initArgs.stopTime initialized initialStored final,
    terminated, discharged, ownersAfter, freed, ?_⟩
  intro query notRecord notEvent notTerminate notEarly notLast notFlag
  have field (name : String) : query ≠ p.member name := by
    intro same
    exact notRecord (same ▸ p.member_in_record name)
  have stateOutside : query ≠ StateProofs.stateAddress p := by
    intro same
    exact notRecord (same ▸ (p.member_in_record "model").member "x")
  have outside : CSHistory.Outside p buffers query :=
    ⟨stateOutside, field "time", notEvent, notTerminate, notEarly, notLast⟩
  exact (framed query outside (field "mode") (field "timeMin") (field "eventTime")
    (field "lastCompleted") (field "stop") (field "stopDefined") notFlag).trans
      (createdFrame query notRecord notFlag)

end Rumoca.FMI3
end
