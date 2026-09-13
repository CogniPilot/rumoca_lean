import Rumoca.FMI3StaticLifecycle
import Rumoca.FMI3InitializationCalls
import RumocaFMI3.StaticFactoryAcquisition
import RumocaFMI3.MELifecycle

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CLiteral CStringMemory StaticFactory

/-- From available static storage, the actual adapter creates an ME instance,
initializes it, executes its admitted control history, terminates and releases
it. The source default, output storage, ownership and every successive call
are derived; no created or initialized heap is an input premise. Importer
integration, failures between calls and concurrent histories remain separate. -/
theorem adapter_create_me_release (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (instances flags : Nat) (separate : instances ≠ flags)
        (before : Heap) (firstBlock : Nat) (signed : Bool),
        let objects := StaticRuntime.objects instances flags separate
        let literals := pool.addresses firstBlock
        letI : CInterface := executionInterface objects literals
        ∀ (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        Identity.Bindings program →
        program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag rfl) →
        program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
        ∀ (args : FactoryArguments.Raw) (heap : Heap),
        CReadOnly.Preserves (pool.install before firstBlock signed) heap →
        CreationStorage heap objects.instances objects.flags objects.capacity →
        ∀ (name supplied : Address) (nameBytes tokenBytes : List UInt8),
        args.name = some name → args.token = some supplied →
        Contents heap name nameBytes → Contents heap supplied tokenBytes →
        nameBytes.length < 2^64 →
        Identity.accepted nameBytes (content " \t\n\r\u000c\u000b") tokenBytes
          (token a.solve.prepareFMI3).toUTF8.data.toList = true →
        ∀ (owners : SlotOwners.State objects.capacity),
        SlotOwners.Represents objects.flagsBlock heap owners →
        (∃ slot, owners slot = none) →
        ∀ (owner : Nat) (initArgs : Initialization.Arguments) (addresses : String → Address)
          (actions : List MEHistory.Action) (final : MEHistory.ReferenceState),
        initArgs.Admissible → MEHistory.Buffers heap addresses →
        MEHistory.Buffers.Outside objects.instances addresses →
        MEHistory.ReferenceTrace (MEHistory.ReferenceState.initial initArgs.start initArgs.stopTime) actions final →
        ∃ trace : List CAtomicBoolean.Calls.Event, ∃ slot : Fin objects.capacity,
        ∃ live after finalClock, ∃ initial : Binary64.Value,
          let p := objects.instances.index slot.val
          let entered := InitializationEntry.finalHeap live p initArgs
          let exited := InitializationCalls.exitedHeap live p initArgs .me
          let terminated := LifecycleBodies.writeMode after p .terminated
          let released := replace terminated (AtomicSlots.address objects.flagsBlock slot) (CAtomicBoolean.cell false)
          trace.length ≤ objects.capacity ∧
          SlotOwners.reserve owners slot owner = some (SlotOwners.update owners slot (some owner)) ∧
          Created live objects.instances objects.flagsBlock (SlotOwners.update owners slot (some owner))
            slot owner .me args.environment args.logger args.logging ∧
          Binary64.value initial = (a.solve.initial.initial : ℝ) ∧
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling (FactoryArguments.signature .me).name (FactoryArguments.arguments .me args) heap .done) behavior ↔
            behavior = .terminates (trace.map tag) ⟨.pointer (some p), live⟩) ∧
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling InitializationCalls.signature.name
              (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite initArgs)) live .done) behavior ↔
            behavior = .terminates [] ⟨.integer 0, entered⟩) ∧
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) entered .done) behavior ↔
            behavior = .terminates [] ⟨.integer 0, exited⟩) ∧
          MEHistory.Calls program p addresses exited actions after ∧
          MEHistory.Stored after p finalClock final ⟨initial⟩ addresses ∧
          InitializationCalls.SourceInitialized a.parsed.ast after p initArgs.start
            (Initialization.trajectory (Binary64.value initArgs.start) (Binary64.value initial)) ∧
          (∀ candidate, InitializationCalls.SourceInitialized a.parsed.ast after p initArgs.start candidate →
            candidate = Initialization.trajectory (Binary64.value initArgs.start) (Binary64.value initial)) ∧
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling Termination.signature.name [.pointer (some p)] after .done) behavior ↔
            behavior = .terminates [] ⟨.integer 0, terminated⟩) ∧
          SlotOwners.release (SlotOwners.update owners slot (some owner)) slot owner = some owners ∧
          SlotOwners.Represents objects.flagsBlock released owners ∧
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling StaticRelease.function.signature.name [.pointer (some p)] terminated .done) behavior ↔
            behavior = .terminates [tag (.write (AtomicSlots.address objects.flagsBlock slot) false)] ⟨.void, released⟩) ∧
          (∀ query, ¬ p.InRecord query →
            (∀ name ∈ DiscreteCalls.names, query ≠ addresses name) →
            query ≠ AtomicSlots.address objects.flagsBlock slot → released query = heap query) := by
  obtain ⟨signatures, unique, _, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, initialization, _, factories, runtime, termination, time, entries, completed, discrete⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E instances flags separate before firstBlock signed
  let objects := StaticRuntime.objects instances flags separate
  let literals := pool.addresses firstBlock
  letI : CInterface := executionInterface objects literals
  dsimp only
  intro program tag actual identity exchange write args heap literalFrame ready name supplied nameBytes tokenBytes
    nameBound tokenBound nameStored tokenStored fits accepted owners represented available owner initArgs
    addresses actions final admissible buffers outside admitted
  obtain ⟨request⟩ := prepared_static_identity a signatures (factories.member .cs) made before firstBlock signed heap
    literalFrame .me args name supplied nameBytes tokenBytes (Or.inl rfl)
    nameBound tokenBound nameStored tokenStored fits accepted
  have reserveBindings : ReservationBindings program tag :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, exchange, by rw [actual]; exact StaticRuntime.reservation_bound _ signatures⟩
  obtain ⟨trace, slot, live, work, reserved, created, preserved, createdFrame, creation⟩ :=
    public_create_owned objects literals program tag identity _ .me args heap request
      (by rw [actual]; exact StaticRuntime.factory_bound _ signatures unique .me (factories.member .me))
      (by rw [actual]; exact StaticRuntime.identity_bound _ signatures) ready reserveBindings
      owners represented available owner
  have initQuiet : InitializationCalls.QuietExecutionContract program := by
    apply StaticInitialization.quiet_correct objects literals a.solve.prepareFMI3 program
    · rw [actual, ← InitializationCalls.function_eq a.solve.prepareFMI3]
      exact LiteralPreparation.function_bound _ signatures unique _ initialization.enterMember
    · rw [actual]
      exact LiteralPreparation.function_bound _ signatures unique _ initialization.exitMember
  have quiet : MEHistory.Quiet program :=
    ⟨(time.prepared pool made).quiet E objects firstBlock program actual,
      fun entry => ((entries entry).prepared pool made).quiet E objects firstBlock program actual,
      (completed.prepared pool made).quiet E objects firstBlock program actual,
      (discrete.prepared pool made).quiet E objects firstBlock program actual⟩
  have releaseBindings : StaticRelease.Bindings program tag :=
    ⟨by rw [actual]; exact runtime.release_defined, rfl, rfl, rfl, rfl, rfl, rfl, write⟩
  have finish := MEHistory.release_correct objects program tag quiet
    (Termination.terminate_release objects literals program tag
      ((termination.prepared pool made).quiet E objects firstBlock program actual) releaseBindings)
  obtain ⟨initial, loaded, agreement, _, _⟩ := created.source_default a (Binary64.value initArgs.start)
  obtain ⟨entered, exited, after, finalClock, called, storedAfter, terminated, discharged, ownersAfter, freed, framed⟩ :=
    MEHistory.initialize_release objects program tag initQuiet finish live slot _ owner initArgs ⟨initial⟩
      addresses actions final admissible (StaticInitialization.entry_storage created.initialized)
      created.initialized.kindValue loaded (buffers.storage_preserved preserved) outside admitted
      created.represented created.owned created.metadata
  have restored := SlotOwners.release_reserved_restore reserved
  rw [restored] at discharged ownersAfter
  refine ⟨trace, slot, live, after, finalClock, initial, work, reserved, created, agreement,
    creation, entered, exited, called, storedAfter, ?_, ?_, terminated, discharged, ownersAfter, freed, ?_⟩
  · exact InitializationCalls.model_source_initialized a.parsed.ast after _ initArgs.start ⟨initial⟩
      a.solve.dae.flat.resolved storedAfter.modelStored
  · intro candidate initialized
    exact InitializationCalls.source_initialized_unique initialized storedAfter.modelStored
  · intro query notRecord notOutputs notFlag
    have field (name : String) : query ≠ (objects.instances.index slot.val).member name := by
      intro same
      exact notRecord (same ▸ (objects.instances.index slot.val).member_in_record name)
    have notHistory : MEHistory.Outside (objects.instances.index slot.val) addresses query :=
      ⟨field "time", field "mode", field "eventTime", field "timeMin", field "lastCompleted", notOutputs⟩
    exact (framed query notHistory (field "stop") (field "stopDefined") notFlag).trans
      (createdFrame query notRecord notFlag)

end Rumoca.FMI3
