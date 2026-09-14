import Rumoca.FMI3CSRunLogging
import Rumoca.FMI3StaticLifecycle
import RumocaFMI3.FactoryEnvironment
import RumocaFMI3.CSCreationStorage
import RumocaFMI3.CSRunFinish
import RumocaFMI3.CSRunStatus

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CLiteral CStringMemory StaticFactory

/-- Actual creation establishes a branching callback-enabled CS lifetime.
Every completed actual history admits mode-appropriate release from the
original lease. The callback frame is universal, and no callback return or
final heap is presumed. Private logger storage may change. -/
theorem adapter_create_logged_cs_release (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (header : CFenv.Header) (instances flags : Nat) (separate : instances ≠ flags)
        (before : Heap) (firstBlock : Nat) (signed : Bool),
        let objects := StaticRuntime.objects instances flags separate
        let literals := pool.addresses firstBlock
        letI : CInterface := RuntimeEnvironment.interface header objects literals
        ∀ (program : CCalls.Events.Program CCalls.Events.Invocation)
          (tag : CAtomicBoolean.Calls.Event → CCalls.Events.Invocation)
          (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31) (logger : CSRun.Logger),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        Identity.Bindings program →
        program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag rfl) →
        program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
        program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
        program.externals "floor" = some (CMathCalls.floorExternal rfl) → logger.Bound program →
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
          (actions : List CSRun.Action) (final : CSRun.Reference) (statuses : List Int),
        initArgs.Admissible → StepArguments.Storage heap objects.instances buffers →
        logger.Respects objects buffers → args.logger = some logger.pointer →
        args.logging = true → args.environment = logger.environment →
        CSRun.ReferenceTrace header objects.instances buffers (CSRun.Reference.restart initArgs) actions final statuses →
        ∃ trace : List CAtomicBoolean.Calls.Event, ∃ slot : Fin objects.capacity,
        ∃ live,
          let p := objects.instances.index slot.val
          let entered := InitializationEntry.finalHeap live p initArgs
          let exited := InitializationCalls.exitedHeap live p initArgs .cs
          let initialTrajectory := Initialization.trajectory (Binary64.value initArgs.start) (Binary64.value Binary64.positiveZero)
          trace.length ≤ objects.capacity ∧
          SlotOwners.reserve owners slot owner = some (SlotOwners.update owners slot (some owner)) ∧
          Created live objects.instances objects.flagsBlock (SlotOwners.update owners slot (some owner))
            slot owner .cs args.environment args.logger args.logging ∧
          Binary64.value Binary64.positiveZero = (a.solve.initial.initial : ℝ) ∧
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
          InitializationCalls.SourceInitialized a.parsed.ast exited p initArgs.start initialTrajectory ∧
          (∀ candidate, InitializationCalls.SourceInitialized a.parsed.ast exited p initArgs.start candidate → candidate = initialTrajectory) ∧
          CSRun.LoggedTrace objects logger (SlotOwners.update owners slot (some owner)) a.solve
            program p buffers exited (CSRun.Reference.restart initArgs) actions final statuses ∧
          (∀ observedStatuses events after, CSRun.Completed program p exited actions observedStatuses events after →
            let released := CSRun.releasedHeap after objects slot final.mode
            observedStatuses = statuses ∧ CSRun.Stored a.solve after p buffers final ∧
            (∃! trajectory, CSRun.SourceEpoch a.parsed.ast final trajectory) ∧
            (∀ trajectory, CSRun.SourceEpoch a.parsed.ast final trajectory →
              ∃ value : Binary64.Value, load after (StateProofs.stateAddress p) = some (.finite value) ∧
                |Binary64.value value - trajectory (Binary64.value final.current.time)| ≤
                  (final.current.elapsed : ℝ) +
                    |Binary64.value final.current.time - (Binary64.value final.start + (final.current.elapsed : ℝ))|) ∧
            CSRun.Released objects program tag after slot (SlotOwners.update owners slot (some owner)) owner final.mode ∧
            SlotOwners.release (SlotOwners.update owners slot (some owner)) slot owner = some owners ∧
            SlotOwners.Represents objects.flagsBlock released owners ∧
            (∀ query, CSRun.Protected objects buffers query → CSRun.Outside p buffers query →
              query ≠ AtomicSlots.address objects.flagsBlock slot → released query = heap query)) := by
  obtain ⟨signatures, unique, resetMember, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, initialization, _, factories, runtime, termination, _, _, _, _, step⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro header instances flags separate before firstBlock signed
  let objects := StaticRuntime.objects instances flags separate
  let literals := pool.addresses firstBlock
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  dsimp only
  intro program tag range logger actual identity exchange write rounding floorBound callbackBound args heap literalFrame ready
    name supplied nameBytes tokenBytes supported nameBound tokenBound nameStored tokenStored fits accepted
    owners represented available owner initArgs buffers actions final statuses admissible outputStorage policy loggerArg loggingArg environmentArg admitted
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
  have reset : StaticReset.ExecutionContract program := by
    apply ResetEnvironment.execution_correct header objects literals a.solve.prepareFMI3 program
    rw [actual]
    exact LiteralPreparation.function_bound _ signatures unique _ resetMember
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
  have state := created.initialized.state_cell Binary64.positiveZero created.initialized.model
  have outputs := (outputStorage.storage_preserved preserved).at_index slot.val
  obtain ⟨entered, exited⟩ := InitializationEnvironment.calls header objects literals a.solve.prepareFMI3
    program live p initArgs .cs enterDefined exitDefined admissible
    (StaticInitialization.entry_storage created.initialized) created.initialized.kindValue
  let initialHeap := InitializationCalls.exitedHeap live p initArgs .cs
  have initialStored : CSRun.Stored a.solve initialHeap p buffers (CSRun.Reference.restart initArgs) :=
    CSRun.Stored.initialized a.solve Binary64.positiveZero live p initArgs buffers admissible
      created.initialized.kindValue state outputs
  have initialLogging : logger.Stored initialHeap p :=
    (CSRun.initialize_retains live p initArgs).logger
      ⟨by simpa only [loggerArg] using created.initialized.loggerValue,
        by simpa only [loggingArg, CBody.boolean] using created.initialized.loggingValue,
        by simpa only [environmentArg] using created.initialized.environmentValue⟩
  have initialLiterals : CReadOnly.Preserves (pool.install before firstBlock signed) initialHeap :=
    literalFrame.trans ((CCalls.Events.termination_preserves ((creation _).mpr rfl)).trans
      ((CCalls.Events.termination_preserves ((entered _).mpr rfl)).trans
        (CCalls.Events.termination_preserves ((exited _).mpr rfl))))
  have actualTrace := admitted.rehandle p
  have ownersAfterInit := StaticInitialization.exited_owners objects live slot initArgs .cs _ created.represented
  have certified := CSRun.logged_trace_correct header objects a.solve.prepareFMI3 signatures pool
    (step.prepared pool made) before firstBlock signed p buffers rfl program range logger actual rounding floorBound
      callbackBound policy reset enterDefined exitDefined initialHeap _ final actions statuses
      (SlotOwners.update owners slot (some owner)) initialLiterals initialStored initialLogging ownersAfterInit actualTrace
  have initialized := InitializationCalls.exited_source_initialized a.solve.prepareFMI3 live p initArgs .cs
    ⟨Binary64.positiveZero⟩ created.initialized.model
  have uniqueInitial := InitializationBodies.exit_model (InitializationEntry.model created.initialized.model initArgs) .cs
  have agreement : Binary64.value Binary64.positiveZero = (a.solve.initial.initial : ℝ) := by
    have units : Binary64.units Binary64.positiveZero = 0 := by decide +kernel
    simp only [Binary64.value, units, Int.cast_zero, zero_div, a.solve.initial_default, Nat.cast_zero]
  refine ⟨trace, slot, live, work, reserved, created, agreement, creation, entered, exited,
    initialized, fun _ given => InitializationCalls.source_initialized_unique given uniqueInitial,
    certified, ?_⟩
  intro observedStatuses events after completed
  have statusesMatch := certified.statuses_eq completed
  subst observedStatuses
  obtain ⟨finalStored, _, ownership, retained, _, runFrame⟩ := certified.completed completed
  have metadataAfter : load after (p.member "slot") = some (.integer slot.val) := by
    rw [load, retained "slot" (by simp)]
    exact (StaticInitialization.exited_metadata live p initArgs .cs).trans created.metadata
  have released := CSRun.finish_correct objects program tag finish releaseBindings rfl a.solve after slot buffers final
    (SlotOwners.update owners slot (some owner)) owner finalStored
    (actualTrace.can_finish (Or.inl rfl)) ownership created.owned metadataAfter
  have discharge := released.discharged
  have restoredOwners := released.ownersAfter
  rw [SlotOwners.release_reserved_restore reserved] at discharge restoredOwners
  refine ⟨rfl, finalStored, CSRun.source_epoch a.solve final, fun _ epoch => finalStored.source_observation epoch,
    released, discharge, restoredOwners, ?_⟩
  intro query isProtected outside notFlag
  exact (released.frame query (outside.field "mode") notFlag).trans
    ((runFrame query isProtected outside).trans ((CSRun.initialize_frame live p query initArgs outside.1).trans
      (createdFrame query outside.1 notFlag)))

end Rumoca.FMI3
end
