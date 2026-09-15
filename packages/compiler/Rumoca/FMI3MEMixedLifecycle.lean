import RumocaFMI3.CSCreationStorage
import Rumoca.FMI3MEMixedRun
import Rumoca.FMI3StaticLifecycle
import RumocaFMI3.FactoryEnvironment
import RumocaFMI3.MEMixedLifecycle
import RumocaFMI3.InitializationStorage
import RumocaFMI3.LoggingCapabilityCreation

noncomputable section
namespace Rumoca.FMI3.MEMixedRun
open CTree CMemory CLiteral CStringMemory StaticFactory CCalls.Events

/-- Actual creation establishes the handle, source default and lease before
the importer selects a mixed ME history. Every completed history, including
errors, callbacks and resets, admits release with the original owner map.
No created heap, future storage, callback return or expected status is assumed. -/
theorem runtime_create_release (compiled : compile input = .ok a)
    (build : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    DerivativeMetadata.Contract a.parsed.ast metadata ∧
    CountMetadata.Contract a.solve.prepareFMI3 metadata ∧
    NominalMetadata.Contract a.parsed.ast metadata ∧
    DebugLogging.MetadataContract metadata "logStatus" ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      MEEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      (∀ events, CountEnvironment.PreparedContract a.solve.prepareFMI3 sigs events pool) ∧
      NominalEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      DebugLogging.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      ∀ (header : CFenv.Header) (instances flags : Nat) (separate : instances ≠ flags)
        (before : Heap) (firstBlock : Nat) (signed : Bool),
        let objects := StaticRuntime.objects instances flags separate
        let literals := pool.addresses firstBlock
        letI : CInterface := RuntimeEnvironment.interface header objects literals
        ∀ (program : Program Invocation) (tag : CAtomicBoolean.Calls.Event → Invocation),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs →
        Identity.Bindings program →
        program.externals "strcmp" = some (CStringCalls.compareExternal (by rfl)) →
        program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag rfl) →
        program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
        ∀ (args : FactoryArguments.Raw) (heap : Heap),
        CReadOnly.Preserves (pool.install before firstBlock signed) heap →
        CreationStorage heap objects.instances objects.flags objects.capacity →
        ∀ (name supplied : Address) (nameBytes tokenBytes : List UInt8),
        args.name = some name → args.token = some supplied →
        Contents heap name nameBytes → Contents heap supplied tokenBytes → nameBytes.length < 2^64 →
        Identity.accepted nameBytes (content " \t\n\r\u000c\u000b") tokenBytes
          (token a.solve.prepareFMI3).toUTF8.data.toList = true →
        ∀ (owners : SlotOwners.State objects.capacity),
        SlotOwners.Represents objects.flagsBlock heap owners → (∃ slot, owners slot = none) →
        ∀ owner : Nat,
        ∃ trace : List CAtomicBoolean.Calls.Event, ∃ slot : Fin objects.capacity,
        ∃ live, ∃ initial : Binary64.Value,
          let p := objects.instances.index slot.val
          trace.length ≤ objects.capacity ∧
          SlotOwners.reserve owners slot owner = some (SlotOwners.update owners slot (some owner)) ∧
          Created live objects.instances objects.flagsBlock (SlotOwners.update owners slot (some owner))
            slot owner .me args.environment args.logger args.logging ∧
          Binary64.value initial = (a.solve.initial.initial : ℝ) ∧
          (∀ behavior, (machine program).Behaves
            (.calling (FactoryArguments.signature .me).name (FactoryArguments.arguments .me args) heap .done) behavior ↔
            behavior = .terminates (trace.map tag) ⟨.pointer (some p), live⟩) ∧
          (∀ (initArgs : Initialization.Arguments) (capability : Logging.Capability)
            (addresses : String → Address) (buffer : Address) (actions : List Action)
            (final : MENumericalHistory.ReferenceState) (finalClock : Time.Clock),
            initArgs.Admissible → MENumericalHistory.CallerStorage heap objects.instances addresses buffer →
            capability.Describes args → capability.Bound program →
            capability.Requires (fun _ effect => MEFailure.Respects effect objects addresses buffer) →
            ReferenceTrace buffer (MENumericalHistory.ReferenceState.initial initArgs initial)
              (Time.Clock.initial initArgs.start) actions final finalClock →
            (∀ action ∈ actions, action.Prepared objects heap addresses buffer) →
            (∀ action ∈ actions, capability.Requires (fun _ effect =>
              ∀ args before value after, effect.execute args before value after →
                CStorage.PreservesOn action.CallerRegion before after)) →
            (∀ action ∈ actions, capability.Requires (fun _ effect =>
              ∀ args before value after, effect.execute args before value after →
                ∀ q, action.ReaderRegion q → after q = before q)) →
            (∀ action ∈ actions, ∀ q, action.ReaderRegion q →
              ¬ p.InRecord q ∧ (∀ name ∈ DiscreteCalls.names, q ≠ addresses name) ∧ q ≠ buffer) →
            (∀ writer ∈ actions, ∀ reader ∈ actions, ∀ q, reader.ReaderRegion q → ¬ writer.CallerRegion q) →
            let entered := InitializationEntry.finalHeap live p initArgs
            let exited := InitializationCalls.exitedHeap live p initArgs .me
            let trajectory := Initialization.trajectory (Binary64.value initArgs.start) (Binary64.value initial)
            (∀ behavior, (machine program).Behaves
              (.calling InitializationCalls.signature.name
                (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite initArgs)) live .done) behavior ↔
              behavior = .terminates [] ⟨.integer 0, entered⟩) ∧
            (∀ behavior, (machine program).Behaves
              (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) entered .done) behavior ↔
              behavior = .terminates [] ⟨.integer 0, exited⟩) ∧
            InitializationCalls.SourceInitialized a.parsed.ast exited p initArgs.start trajectory ∧
            (∀ candidate, InitializationCalls.SourceInitialized a.parsed.ast exited p initArgs.start candidate →
              candidate = trajectory) ∧
            Trace a.solve.prepareFMI3 objects (SlotOwners.update owners slot (some owner)) capability program p addresses buffer
              exited args.logging (MENumericalHistory.ReferenceState.initial initArgs initial)
              (Time.Clock.initial initArgs.start) actions final finalClock ∧
            ((∃ observed after epochs, Completed program p addresses buffer exited actions observed after epochs) ∨
              Stopped program p addresses buffer exited actions) ∧
            (∀ stop, Interrupted program p addresses buffer exited actions stop →
              SourcePrefix a.solve capability args.logging exited p addresses buffer (MENumericalHistory.ReferenceState.initial initArgs initial)
                (Time.Clock.initial initArgs.start) actions stop) ∧
            (∀ observed after epochs, Completed program p addresses buffer exited actions observed after epochs →
              MENumericalHistory.Stored after p finalClock final addresses buffer ∧ Reset.Storage after p ∧
              capability.Configured after p ((loggingUpdate actions).getD args.logging) ∧
              InitializationProtocol.Retention (loggingUpdate actions) p live after ∧
              SourceObservations a.solve actions observed ∧
              MENumericalRun.InitializedEpochs a.parsed.ast p epochs ∧ CReadOnly.Preserves heap after ∧
              LifecycleRelease.Released objects program tag after slot (SlotOwners.update owners slot (some owner))
                owner .me final.control.mode ∧
              SlotOwners.release (SlotOwners.update owners slot (some owner)) slot owner = some owners ∧
              SlotOwners.Represents objects.flagsBlock (LifecycleRelease.releasedHeap after objects slot final.control.mode) owners ∧
              (∀ q, MEFailure.Protected objects addresses buffer q → ¬ p.InRecord q →
                (∀ name ∈ DiscreteCalls.names, q ≠ addresses name) → q ≠ buffer →
                q ≠ AtomicSlots.address objects.flagsBlock slot →
                LifecycleRelease.releasedHeap after objects slot final.control.mode q = heap q))) := by
  obtain ⟨sigs, unique, resetMember, printed, _, functions, _, _, queries, ready, _, _, _, nominalContract, states, derivative,
    _, _, initialization, _, factories, runtime, termination, time, entries, completed, discrete, _, loggingContract, _⟩ := build.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  have counts : ∀ events, CountEnvironment.PreparedContract a.solve.prepareFMI3 sigs events pool := by
    letI : StaticLiterals := ⟨fun _ => none⟩
    exact fun events => (queries inferInstance events).prepared pool made
  have nominals := nominalContract.runtime pool made
  have logging := loggingContract.prepared pool made
  have prepared : MEEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool :=
    ⟨StateEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique states.member made,
      DerivativeEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique derivative.member derivative.numerical.fresh made,
      MEControlEnvironment.TimeControl.prepared_correct a.solve.prepareFMI3 sigs unique time.member made,
      fun entry => MEControlEnvironment.EntryControl.prepared_correct a.solve.prepareFMI3 entry sigs
        unique (entries entry).member made,
      MEControlEnvironment.CompletedControl.prepared_correct a.solve.prepareFMI3 sigs unique completed.member made,
      MEControlEnvironment.DiscreteControl.prepared_correct a.solve.prepareFMI3 sigs unique discrete.member made⟩
  refine ⟨compiled, build.numerical, DerivativeMetadata.artifact_derivatives _ _ build.metadata,
    CountMetadata.artifact_counts _ _ build.metadata, NominalMetadata.artifact_nominals _ _ build.metadata,
    DebugLogging.artifact_category _ _ build.metadata, sigs, pool, made, printed, functions, prepared, counts, nominals, logging, ?_⟩
  intro header instances flags separate before firstBlock signed
  let objects := StaticRuntime.objects instances flags separate
  let literals := pool.addresses firstBlock
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  dsimp only
  intro program tag actual identity compare exchange write args heap literalFrame storage name supplied nameBytes tokenBytes
    nameBound tokenBound nameStored tokenStored fits accepted owners represented available owner
  obtain ⟨request⟩ := prepared_static_identity a sigs (factories.member .cs) made before firstBlock signed heap
    literalFrame .me args name supplied nameBytes tokenBytes (Or.inl rfl)
    nameBound tokenBound nameStored tokenStored fits accepted
  have reserveBindings : ReservationBindings program tag :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, exchange, by rw [actual]; exact StaticRuntime.reservation_bound _ sigs⟩
  obtain ⟨trace, slot, live, work, reserved, created, preserved, createdFrame, creation⟩ :=
    FactoryEnvironment.create_owned header objects literals program tag identity _ .me args heap request
      (by rw [actual]; exact StaticRuntime.factory_bound _ sigs unique .me (factories.member .me))
      (by rw [actual]; exact StaticRuntime.identity_bound _ sigs) storage reserveBindings
      owners represented available owner
  let p := objects.instances.index slot.val
  have enterDefined : program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) := by
    rw [actual, ← InitializationCalls.function_eq a.solve.prepareFMI3]
    exact LiteralPreparation.function_bound _ sigs unique _ initialization.enterMember
  have exitDefined : program.internal.definitions InitializationExit.signature.name =
      some (.tree (Runtime.function a.solve.prepareFMI3 InitializationExit.signature)) := by
    rw [actual]
    exact LiteralPreparation.function_bound _ sigs unique _ initialization.exitMember
  have releaseBindings : StaticRelease.Bindings program tag :=
    ⟨by rw [actual]; exact runtime.release_defined, rfl, rfl, rfl, rfl, rfl, rfl, write⟩
  have terminateQuiet : Termination.QuietContract program := by
    apply TerminationEnvironment.quiet_correct header objects literals a.solve.prepareFMI3 program
    rw [actual]
    exact LiteralPreparation.function_bound _ sigs unique _ termination.member
  have finish := TerminationEnvironment.release_correct header objects literals program tag terminateQuiet releaseBindings
  have reset : StaticReset.ExecutionContract program := by
    apply ResetEnvironment.execution_correct header objects literals a.solve.prepareFMI3 program
    rw [actual]
    exact LiteralPreparation.function_bound _ sigs unique _ resetMember
  obtain ⟨initial, loaded, agreement, _, _⟩ := created.source_default a 0
  have state := created.initialized.state_cell initial loaded
  refine ⟨trace, slot, live, initial, work, reserved, created, agreement, creation, ?_⟩
  intro initArgs capability addresses buffer actions final finalClock admissible callers matching bound required admitted requests
    policies readPolicies guarded separateReaders
  have outputs := (callers.storage_preserved preserved).at_index slot.val
  obtain ⟨entered, exited⟩ := InitializationEnvironment.calls header objects literals a.solve.prepareFMI3
    program live p initArgs .me enterDefined exitDefined admissible
    (StaticInitialization.entry_storage created.initialized) created.initialized.kindValue
  let initializedHeap := InitializationCalls.exitedHeap live p initArgs .me
  have initialStored := MENumericalHistory.initialized_stored live p initArgs initial addresses buffer admissible
    created.initialized.kindValue state outputs
  have initialReset := MENumericalHistory.initialized_reset_storage live p initArgs initial state
  have initRetains : InitializationProtocol.Retains p live initializedHeap := by
    intro name retained
    have different (field : String) (member : field ∈ InitializationAccess.writtenFields) :
        p.member name ≠ p.member field := by
      intro same
      exact retained ((Address.member_inj _ _ _).mp same ▸ member)
    exact InitializationCalls.exited_frame live p (p.member name) initArgs .me
      (different "time" (by decide)) (different "timeMin" (by decide))
      (different "eventTime" (by decide)) (different "lastCompleted" (by decide))
      (different "stop" (by decide)) (different "stopDefined" (by decide)) (different "mode" (by decide))
  have initialRetention := InitializationProtocol.Retention.of_retains initRetains
  have initialConfig := (Logging.Capability.created matching created).initialization_retained initRetains
  have initialWritable := initialRetention.writable created.initialized.storage.logging
  have initialOwners := StaticInitialization.exited_owners objects live slot initArgs .me _ created.represented
  have prefixReadonly : CReadOnly.Preserves heap initializedHeap :=
    (termination_preserves ((creation _).mpr rfl)).trans
      ((termination_preserves ((entered _).mpr rfl)).trans (termination_preserves ((exited _).mpr rfl)))
  have enteredStorage := (InitializationStorage.entered live p initArgs .me admissible
    (StaticInitialization.entry_storage created.initialized) created.initialized.kindValue).1
  have exitedStorage := (InitializationStorage.exited (InitializationEntry.finalHeap live p initArgs) p .me
    (InitializationCalls.entered_mode live p initArgs)).1
  have readOutside : ∀ action ∈ actions, ∀ q, action.ReaderRegion q →
      MENumericalRun.Outside p addresses buffer q ∧ q ≠ p.member "logging" := by
    intro action member q inside
    obtain ⟨notRecord, notOutputs, notBuffer⟩ := guarded action member q inside
    have field (name : String) : q ≠ p.member name := by
      intro same
      exact notRecord (same ▸ p.member_in_record name)
    have stateOutside : q ≠ StateProofs.stateAddress p := by
      intro same
      exact notRecord (same ▸ (p.member_in_record "model").member "x")
    exact ⟨⟨⟨⟨field "time", field "mode", field "eventTime", field "timeMin", field "lastCompleted", notOutputs⟩,
      stateOutside, notBuffer⟩, field "stop", field "stopDefined"⟩, field "logging"⟩
  have current : ∀ action ∈ actions, action.Prepared objects initializedHeap addresses buffer := by
    intro action member
    exact Action.Prepared.preserved action (requests action member)
      ((preserved.trans (enteredStorage.trans exitedStorage)).on action.CallerRegion) (by
        intro q inside
        have notRecord := (guarded action member q inside).1
        have field (name : String) : q ≠ p.member name := by
          intro same
          exact notRecord (same ▸ p.member_in_record name)
        have notFlag : q ≠ AtomicSlots.address objects.flagsBlock slot := by
          cases action with
          | run _ | reject _ _ | counts _ | nominals _ => cases inside
          | logging request =>
            have borrowed : InitializationProtocol.ReadBank.Stored [request] heap := by
              intro selected selectedMember
              have same : selected = request := by simpa only [List.mem_singleton] using selectedMember
              subst selected
              exact requests (.logging request) member
            exact InitializationProtocol.ReadBank.Stored.not_flag (objects := objects) borrowed represented ⟨request, by simp, inside⟩ slot
        exact (InitializationCalls.exited_frame live p q initArgs .me (field "time") (field "timeMin")
          (field "eventTime") (field "lastCompleted") (field "stop") (field "stopDefined") (field "mode")).trans
          (createdFrame q notRecord notFlag))
  have certified := trace_correct header objects a.solve.prepareFMI3 sigs pool prepared counts nominals logging before firstBlock signed
    program capability args.logging actual compare bound reset enterDefined exitDefined initializedHeap p _ _ final finalClock addresses buffer actions
    (SlotOwners.update owners slot (some owner)) required initialConfig initialWritable rfl initialOwners
    (literalFrame.trans prefixReadonly) initialStored initialReset admitted current policies readPolicies readOutside separateReaders
  have initialized := InitializationCalls.exited_source_initialized a.solve.prepareFMI3 live p initArgs .me ⟨initial⟩ loaded
  have initialModel := InitializationBodies.exit_model (InitializationEntry.model loaded initArgs) .me
  refine ⟨entered, exited, initialized,
    fun _ given => InitializationCalls.source_initialized_unique given initialModel,
    certified, certified.progress, ?_, ?_⟩
  · intro stop interrupted
    exact certified.interrupted_source a.solve initialStored initialReset initialConfig initialOwners admitted interrupted
  · intro observed after epochs executed
    obtain ⟨finalStored, finalReset, finalConfig, finalRetention, finalOwners, readonly, frame⟩ := certified.completed executed
    obtain ⟨sourceValues, sourceEpochs⟩ := certified.source a.solve executed
    have metadataAfter : load after (p.member "slot") = some (.integer slot.val) :=
      (certified.slot initialStored rfl executed).trans ((StaticInitialization.exited_metadata live p initArgs .me).trans created.metadata)
    have released := LifecycleRelease.finish_correct objects program tag finish releaseBindings rfl after slot .me final.control.mode
      (SlotOwners.update owners slot (some owner)) owner finalStored.control.kind finalStored.control.mode
      (admitted.can_finish (Or.inl (by simp [MENumericalHistory.ReferenceState.initial,
        MEHistory.ReferenceState.initial, Reference.Allowed]))) finalOwners created.owned metadataAfter
    have discharged := released.discharged
    have restored := released.ownersAfter
    rw [SlotOwners.release_reserved_restore reserved] at discharged restored
    refine ⟨finalStored, finalReset, finalConfig, ?_, sourceValues, sourceEpochs, prefixReadonly.trans readonly,
      released, discharged, restored, ?_⟩
    · have combined := initialRetention.trans finalRetention
      cases update : loggingUpdate actions <;> simpa only [update, Option.orElse] using combined
    intro q guarded notRecord notOutputs notBuffer notFlag
    have field (name : String) : q ≠ p.member name := by
      intro same
      exact notRecord (same ▸ p.member_in_record name)
    have stateOutside : q ≠ StateProofs.stateAddress p := by
      intro same
      exact notRecord (same ▸ (p.member_in_record "model").member "x")
    have outside : MENumericalRun.Outside p addresses buffer q :=
      ⟨⟨⟨field "time", field "mode", field "eventTime", field "timeMin", field "lastCompleted", notOutputs⟩,
        stateOutside, notBuffer⟩, field "stop", field "stopDefined"⟩
    exact (released.frame q (field "mode") notFlag).trans
      ((frame q guarded outside (field "logging")).trans
        ((InitializationCalls.exited_frame live p q initArgs .me (field "time") (field "timeMin")
          (field "eventTime") (field "lastCompleted") (field "stop") (field "stopDefined") (field "mode")).trans
          (createdFrame q notRecord notFlag)))

end Rumoca.FMI3.MEMixedRun
end
