import Rumoca.FMI3CreatedInitializationAccess
import Rumoca.FMI3MEMixedRun
import RumocaFMI3.InitializationMERun
import RumocaFMI3.MEMixedLifecycle
import RumocaFMI3.LifecycleEnvironment
import RumocaC.StorageAtomic
import RumocaFMI3.LoggingCapabilityCreation

noncomputable section
namespace Rumoca.FMI3.InitializationAccess
open CTree CMemory StaticFactory CCalls.Events

/-- The existing mixed ME execution relation starts at the actual exit heap.
Every completed branch retains its source derivative observations, actual reset
checkpoints, and release back to the original owner map. Trial-state writes
are not asserted to lie on the initial source trajectory. -/
def MEContinuation [CInterface] (model : Solve.Model source) (objects : Objects)
    (program : Program Invocation) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (slot : Fin objects.capacity) (owners : SlotOwners.State objects.capacity) (owner : Nat)
    (original exited : Heap) (access : Float64Buffers.Layout)
    (addresses : String → Address) (buffer : Address)
    (initial final : MENumericalHistory.ReferenceState) (clock finalClock : Time.Clock)
    (actions : List MEMixedRun.Action) (capability : Logging.Capability) (enabled : Bool) : Prop :=
  let p := objects.instances.index slot.val
  MEMixedRun.Trace model.prepareFMI3 objects (SlotOwners.update owners slot (some owner)) capability
    program p addresses buffer exited enabled initial clock actions final finalClock ∧
  ∀ observed after epochs,
    MEMixedRun.Completed program p addresses buffer exited actions observed after epochs →
    MENumericalHistory.Stored after p finalClock final addresses buffer ∧ Reset.Storage after p ∧
    capability.Configured after p ((MEMixedRun.loggingUpdate actions).getD enabled) ∧
    InitializationProtocol.Retention (MEMixedRun.loggingUpdate actions) p exited after ∧
    MEMixedRun.SourceObservations model actions observed ∧
    MENumericalRun.InitializedEpochs source p epochs ∧ CReadOnly.Preserves original after ∧
    LifecycleRelease.Released objects program tag after slot (SlotOwners.update owners slot (some owner))
      owner .me final.control.mode ∧
    SlotOwners.release (SlotOwners.update owners slot (some owner)) slot owner = some owners ∧
    SlotOwners.Represents objects.flagsBlock
      (LifecycleRelease.releasedHeap after objects slot final.control.mode) owners ∧
    (∀ q, MEFailure.Protected objects addresses buffer q → ¬ p.InRecord q →
      MENumericalRun.Outside p addresses buffer q →
      Float64Access.Outside access q → q ≠ AtomicSlots.address objects.flagsBlock slot →
      LifecycleRelease.releasedHeap after objects slot final.control.mode q = original q)

theorem Certificate.me_continuation {source : AST.Model} (model : Solve.Model source)
    (header : CFenv.Header) (objects : Objects) (sigs : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model.prepareFMI3 sigs).flatMap CLiteral.functionNames))
    (lifecycle : LifecycleEnvironment.PreparedContract model.prepareFMI3 sigs)
    (prepared : MEEnvironment.PreparedContract model.prepareFMI3 sigs pool)
    (counts : ∀ events, CountEnvironment.PreparedContract model.prepareFMI3 sigs events pool)
    (nominals : NominalEnvironment.PreparedContract model.prepareFMI3 sigs pool)
    (loggingPrepared : DebugLogging.PreparedContract model.prepareFMI3 sigs pool)
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) (slot : Fin objects.capacity)
    (access : Float64Buffers.Layout) (addresses : String → Address) (buffer : Address) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation) (tag : CAtomicBoolean.Calls.Event → Invocation),
    program.internal = LiteralPreparation.program model.prepareFMI3 sigs →
    program.externals "strcmp" = some (CStringCalls.compareExternal (by rfl)) →
    program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
    ∀ (original live beforeEntry atExit : Heap) (state : ModelExchange.State) (args : Initialization.Arguments)
      (before during : List Float64Access.Request) (factoryArgs : FactoryArguments.Raw)
      (owners : SlotOwners.State objects.capacity) (owner : Nat),
    let p := objects.instances.index slot.val
    Certificate model.prepareFMI3 program p access args .me state Binary64.positiveZero live
      before during beforeEntry atExit →
    InstanceInitialization.Initialized live p .me factoryArgs.environment factoryArgs.logger factoryArgs.logging →
    CReadOnly.Preserves (pool.install baseHeap firstBlock signed) original →
    CReadOnly.Preserves original live → CStorage.Preserves original live →
    (∀ q, ¬ p.InRecord q → q ≠ AtomicSlots.address objects.flagsBlock slot → live q = original q) →
    args.Admissible → MENumericalHistory.CallerStorage original p addresses buffer →
    SlotOwners.Represents objects.flagsBlock live (SlotOwners.update owners slot (some owner)) →
    SlotOwners.reserve owners slot owner = some (SlotOwners.update owners slot (some owner)) →
    load live (p.member "slot") = some (.integer slot.val) →
    ∀ (capability : Logging.Capability) (actions : List MEMixedRun.Action)
      (final : MENumericalHistory.ReferenceState) (finalClock : Time.Clock),
    capability.Describes factoryArgs → capability.Bound program →
    capability.Requires (fun _ effect => MEFailure.Respects effect objects addresses buffer) →
    MEMixedRun.ReferenceTrace buffer (meReference state args before during)
      (Time.Clock.initial args.start) actions final finalClock →
    (∀ action ∈ actions, action.Prepared objects original addresses buffer) →
    (∀ action ∈ actions, capability.Requires (fun _ effect => ∀ args before value after,
      effect.execute args before value after → CStorage.PreservesOn action.CallerRegion before after)) →
    (∀ action ∈ actions, capability.Requires (fun _ effect => ∀ args before value after,
      effect.execute args before value after → ∀ q, action.ReaderRegion q → after q = before q)) →
    (∀ action ∈ actions, ∀ q, action.ReaderRegion q → ¬ p.InRecord q ∧
      Float64Access.Outside access q ∧ MENumericalRun.Outside p addresses buffer q) →
    (∀ writer ∈ actions, ∀ reader ∈ actions, ∀ q, reader.ReaderRegion q → ¬ writer.CallerRegion q) →
    MEContinuation model objects program tag slot owners owner original
      (InitializationBodies.exitHeap atExit p .me) access addresses buffer (meReference state args before during)
      final (Time.Clock.initial args.start) finalClock actions capability factoryArgs.logging := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program tag actual compare write original live beforeEntry atExit state args before during factoryArgs owners owner
  let p := objects.instances.index slot.val
  dsimp only
  intro initialized initializedInstance literals liveReadonly liveStorage liveFrame admissible outputs represented
    reserved metadata capability actions final finalClock matching bound required admitted requests policies readPolicies readerOutside separateReaders
  obtain ⟨reset, enterDefined, exitDefined, termination, releaseDefined⟩ :=
    lifecycle.execution header objects (pool.addresses firstBlock) program actual
  have releaseBindings : StaticRelease.Bindings program tag := ⟨releaseDefined, rfl, rfl, rfl, rfl, rfl, rfl, write⟩
  have finish := TerminationEnvironment.release_correct header objects (pool.addresses firstBlock) program tag
    termination releaseBindings
  let exited := InitializationBodies.exitHeap atExit p .me
  have stored := initialized.me_storage admissible (outputs.storage_preserved liveStorage)
  have resetStorage := initializedInstance.storage.toStorage.preserved initialized.storage
  have originalConfig : capability.Configured live p factoryArgs.logging := by
    apply capability.initialized
    simpa only [matching.1, matching.2] using initializedInstance
  have configured := initialized.configuration originalConfig
  have writable := initialized.retention.writable initializedInstance.storage.logging
  have readonly := liveReadonly.trans initialized.readonly
  have ownership := initialized.owners represented
  have current : ∀ action ∈ actions, action.Prepared objects exited addresses buffer := by
    intro action member
    exact MEMixedRun.Action.Prepared.preserved action (requests action member)
      ((liveStorage.trans initialized.storage).on action.CallerRegion) (by
        intro q inside
        obtain ⟨notRecord, accessOutside, _⟩ := readerOutside action member q inside
        have field (name : String) : q ≠ p.member name := fun same => notRecord (same ▸ p.member_in_record name)
        have notState : q ≠ StateProofs.stateAddress p :=
          fun same => notRecord (same ▸ (p.member_in_record "model").member "x")
        have notFlag : q ≠ AtomicSlots.address objects.flagsBlock slot := by
          cases action with
          | run _ | reject _ _ | counts _ | nominals _ => cases inside
          | logging request =>
            have readable := (show request.Inputs original from requests (.logging request) member).load_ne_none inside
            intro same
            subst q
            exact readable (liveStorage.atomic_unreadable (represented slot) rfl)
        exact (initialized.frame q ⟨accessOutside, notState, fun name _ => field name⟩).trans
          (liveFrame q notRecord notFlag))
  have certified := MEMixedRun.trace_correct header objects model.prepareFMI3 sigs pool prepared counts nominals loggingPrepared baseHeap firstBlock signed
    program capability factoryArgs.logging actual compare bound reset enterDefined exitDefined exited p _ _ final finalClock addresses buffer actions
      (SlotOwners.update owners slot (some owner)) required configured writable rfl ownership (literals.trans readonly)
      stored resetStorage admitted current policies readPolicies
      (fun action member q inside => ⟨(readerOutside action member q inside).2.2,
        fun same => (readerOutside action member q inside).1 (same ▸ p.member_in_record "logging")⟩) separateReaders
  refine ⟨certified, ?_⟩
  intro observed after epochs completed
  obtain ⟨finalStored, finalReset, finalConfig, retention, finalOwners, runReadonly, frame⟩ := certified.completed completed
  obtain ⟨sourceValues, sourceEpochs⟩ := certified.source model completed
  have metadataAfter : load after (p.member "slot") = some (.integer slot.val) :=
    (certified.slot stored rfl completed).trans (initialized.metadata.trans metadata)
  have released := LifecycleRelease.finish_correct objects program tag finish releaseBindings rfl after slot .me
    final.control.mode (SlotOwners.update owners slot (some owner)) owner finalStored.control.kind finalStored.control.mode
      (admitted.can_finish (Or.inl (by simp [meReference, MENumericalHistory.ReferenceState.initial,
        MEHistory.ReferenceState.initial, Reference.Allowed]))) finalOwners
      (by simp [SlotOwners.update]) metadataAfter
  have discharged := released.discharged
  have restored := released.ownersAfter
  rw [SlotOwners.release_reserved_restore reserved] at discharged restored
  refine ⟨finalStored, finalReset, finalConfig, retention, sourceValues, sourceEpochs, readonly.trans runReadonly,
    released, discharged, restored, ?_⟩
  intro q guarded notRecord outside accessOutside notFlag
  have field (name : String) : q ≠ p.member name := by
    intro same
    exact notRecord (same ▸ p.member_in_record name)
  have notState : q ≠ StateProofs.stateAddress p := by
    intro same
    exact notRecord (same ▸ (p.member_in_record "model").member "x")
  exact (released.frame q (field "mode") notFlag).trans
    ((frame q guarded outside (field "logging")).trans
      ((initialized.frame q ⟨accessOutside, notState, fun name _ => field name⟩).trans (liveFrame q notRecord notFlag)))

end Rumoca.FMI3.InitializationAccess
end

noncomputable section
namespace Rumoca.FMI3.InitializationAccess
open CTree CMemory CLiteral CStringMemory StaticFactory Float64Access Float64Buffers CCalls.Events

/-- Source-bound creation and accepted initialization accesses supply the
existing mixed ME history. Initial source IVP, raw observations, reset epochs,
and final release all use the actual target heaps and one prepared runtime. -/
theorem runtime_create_me_histories (compiled : compile input = .ok a)
    (build : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    Float64Metadata.Contract a.solve.prepareFMI3 metadata ∧
    Float64SetMetadata.Contract a.parsed.ast metadata ∧
    DerivativeMetadata.Contract a.parsed.ast metadata ∧
    CountMetadata.Contract a.solve.prepareFMI3 metadata ∧
    NominalMetadata.Contract a.parsed.ast metadata ∧
    DebugLogging.MetadataContract metadata "logStatus" ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap CLiteral.functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      LifecycleEnvironment.PreparedContract a.solve.prepareFMI3 sigs ∧
      MEEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      (∀ events, CountEnvironment.PreparedContract a.solve.prepareFMI3 sigs events pool) ∧
      NominalEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      DebugLogging.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      ∀ (header : CFenv.Header) (instances flags : Nat) (separate : instances ≠ flags)
        (baseHeap : Heap) (firstBlock : Nat) (signed : Bool),
        let objects := StaticRuntime.objects instances flags separate
        let literals := pool.addresses firstBlock
        letI : CInterface := RuntimeEnvironment.interface header objects literals
        ∀ (program : Program Invocation) (tag : CAtomicBoolean.Calls.Event → Invocation),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs →
        Identity.Bindings program →
        program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag rfl) →
        program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
        ∀ (factoryArgs : FactoryArguments.Raw) (heap : Heap),
        CReadOnly.Preserves (pool.install baseHeap firstBlock signed) heap →
        CreationStorage heap objects.instances objects.flags objects.capacity →
        ∀ (name supplied : Address) (nameBytes tokenBytes : List UInt8),
        factoryArgs.name = some name → factoryArgs.token = some supplied →
        Contents heap name nameBytes → Contents heap supplied tokenBytes → nameBytes.length < 2^64 →
        Identity.accepted nameBytes (content " \t\n\r\u000c\u000b") tokenBytes
          (token a.solve.prepareFMI3).toUTF8.data.toList = true →
        ∀ (owners : SlotOwners.State objects.capacity),
        SlotOwners.Represents objects.flagsBlock heap owners → (∃ slot, owners slot = none) → ∀ owner : Nat,
        ∃ trace : List CAtomicBoolean.Calls.Event, ∃ slot : Fin objects.capacity,
        ∃ live, ∃ initial : Binary64.Value,
          let p := objects.instances.index slot.val
          trace.length ≤ objects.capacity ∧
          SlotOwners.reserve owners slot owner = some (SlotOwners.update owners slot (some owner)) ∧
          Created live objects.instances objects.flagsBlock (SlotOwners.update owners slot (some owner))
            slot owner .me factoryArgs.environment factoryArgs.logger factoryArgs.logging ∧
          load live (StateProofs.stateAddress p) = some (.finite initial) ∧
          Binary64.value initial = (a.solve.initial.initial : ℝ) ∧
          CStorage.Preserves heap live ∧
          (∀ q, ¬ p.InRecord q → q ≠ AtomicSlots.address objects.flagsBlock slot → live q = heap q) ∧
          (∀ behavior, (machine program).Behaves
            (.calling (FactoryArguments.signature .me).name (FactoryArguments.arguments .me factoryArgs) heap .done) behavior ↔
            behavior = .terminates (trace.map tag) ⟨.pointer (some p), live⟩) ∧
          ∀ (buffers : Layout) (args : Initialization.Arguments) (before during : List Request),
          Stored heap buffers → buffers.Separate objects.instances → args.Admissible →
          (∀ request ∈ before, request.Fits buffers) → (∀ request ∈ before, request.StartQuery) →
          (∀ request ∈ during, request.Fits buffers) → (∀ request ∈ during, request.Allowed .me .initialization) →
          ∃ beforeEntry atExit,
            Certificate a.solve.prepareFMI3 program p buffers args .me ⟨initial⟩ Binary64.positiveZero
              live before during beforeEntry atExit ∧
            Executed program p buffers args live before during
              (expectedObservation a.solve.prepareFMI3 ⟨initial⟩ Binary64.positiveZero args before during)
              (InitializationBodies.exitHeap atExit p .me) ∧
            InitializationCalls.SourceInitialized a.parsed.ast (InitializationBodies.exitHeap atExit p .me) p args.start
              (trajectory ⟨initial⟩ args before during) ∧
            (∀ candidate, InitializationCalls.SourceInitialized a.parsed.ast (InitializationBodies.exitHeap atExit p .me)
              p args.start candidate → candidate = trajectory ⟨initial⟩ args before during) ∧
            (∀ observation after, Executed program p buffers args live before during observation after ↔
              observation = expectedObservation a.solve.prepareFMI3 ⟨initial⟩ Binary64.positiveZero args before during ∧
              after = InitializationBodies.exitHeap atExit p .me) ∧
            ∀ (addresses : String → Address) (buffer : Address) (capability : Logging.Capability)
              (actions : List MEMixedRun.Action) (final : MENumericalHistory.ReferenceState) (finalClock : Time.Clock),
              MENumericalHistory.CallerStorage heap objects.instances addresses buffer →
              capability.Describes factoryArgs → capability.Bound program →
    capability.Requires (fun _ effect => MEFailure.Respects effect objects addresses buffer) →
              MEMixedRun.ReferenceTrace buffer (meReference ⟨initial⟩ args before during)
                (Time.Clock.initial args.start) actions final finalClock →
              (∀ action ∈ actions, action.Prepared objects heap addresses buffer) →
              (∀ action ∈ actions, capability.Requires (fun _ effect => ∀ args before value after,
      effect.execute args before value after → CStorage.PreservesOn action.CallerRegion before after)) →
    (∀ action ∈ actions, capability.Requires (fun _ effect => ∀ args before value after,
      effect.execute args before value after → ∀ q, action.ReaderRegion q → after q = before q)) →
    (∀ action ∈ actions, ∀ q, action.ReaderRegion q → ¬ p.InRecord q ∧
      Float64Access.Outside buffers q ∧ MENumericalRun.Outside p addresses buffer q) →
    (∀ writer ∈ actions, ∀ reader ∈ actions, ∀ q, reader.ReaderRegion q → ¬ writer.CallerRegion q) →
              MEContinuation a.solve objects program tag slot owners owner heap
                (InitializationBodies.exitHeap atExit p .me) buffers addresses buffer (meReference ⟨initial⟩ args before during)
                final (Time.Clock.initial args.start) finalClock actions capability factoryArgs.logging := by
  obtain ⟨compiled, numerical, metadataVariables, writable, sigs, pool, made, printed, functions, csPrepared, prepared, counts, nominals, loggingPrepared, create⟩ :=
    runtime_create_release compiled build
  refine ⟨compiled, numerical, metadataVariables, writable, DerivativeMetadata.artifact_derivatives _ _ build.metadata,
    CountMetadata.artifact_counts _ _ build.metadata, NominalMetadata.artifact_nominals _ _ build.metadata,
    DebugLogging.artifact_category _ _ build.metadata,
    sigs, pool, made, printed, functions, csPrepared.toPreparedContract, prepared, counts, nominals, loggingPrepared, ?_⟩
  intro header instances flags separate baseHeap firstBlock signed
  let objects := StaticRuntime.objects instances flags separate
  let literals := pool.addresses firstBlock
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  dsimp only
  intro program tag actual identity exchange write factoryArgs heap literalFrame storage name supplied nameBytes tokenBytes
    nameBound tokenBound nameStored tokenStored fits accepted owners represented available owner
  obtain ⟨trace, slot, live, initial, work, reserved, created, loaded, agreement, preserved, createdFrame, creation, histories⟩ :=
    create Invocation header instances flags separate baseHeap firstBlock signed program tag actual identity exchange write
      .me factoryArgs heap literalFrame storage name supplied nameBytes tokenBytes (Or.inl rfl)
      nameBound tokenBound nameStored tokenStored fits accepted owners represented available owner
  let p := objects.instances.index slot.val
  refine ⟨trace, slot, live, initial, work, reserved, created, loaded, agreement, preserved, createdFrame, creation, ?_⟩
  intro buffers args before during buffersStored buffersSeparate admissible beforeFits beforeAllowed duringFits duringAllowed
  obtain ⟨beforeEntry, atExit, certified, executed, _⟩ := histories buffers args before during buffersStored buffersSeparate
    admissible beforeFits beforeAllowed duringFits duringAllowed
  obtain ⟨_, initialized, uniqueSource⟩ := certified.completed_source executed
  refine ⟨beforeEntry, atExit, certified, executed, initialized, uniqueSource, fun _ _ => certified.execution_iff, ?_⟩
  intro addresses buffer capability actions final finalClock outputs matching bound required admitted requests policies readPolicies readerOutside separateReaders
  exact certified.me_continuation a.solve header objects sigs pool csPrepared.toPreparedContract prepared counts nominals loggingPrepared
    baseHeap firstBlock signed slot buffers addresses buffer program tag actual identity.compareBinding write heap live beforeEntry atExit ⟨initial⟩ args
      before during factoryArgs owners owner created.initialized literalFrame
      (termination_preserves ((creation _).mpr rfl)) preserved createdFrame admissible (outputs.at_index slot.val)
      created.represented reserved created.metadata capability actions final finalClock matching bound required admitted requests policies readPolicies readerOutside separateReaders

end Rumoca.FMI3.InitializationAccess
end
