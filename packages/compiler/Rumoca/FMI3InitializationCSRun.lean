import Rumoca.FMI3CreatedInitializationAccess
import Rumoca.FMI3CSMixedRun
import RumocaFMI3.CSMixedLifecycle
import RumocaFMI3.InitializationCSRun
import RumocaC.StorageAtomic
import RumocaFMI3.LoggingCapabilityCreation

noncomputable section
namespace Rumoca.FMI3.InitializationAccess
open CTree CMemory StaticFactory CCalls.Events
variable {source : AST.Model} {model : Solve.FMI3Model source}

structure RunOutcome [CInterface] (model : Solve.FMI3Model source) (objects : Objects)
    (program : Program Invocation) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (slot : Fin objects.capacity) (owners : SlotOwners.State objects.capacity) (owner : Nat)
    (original : Heap) (access : Float64Buffers.Layout) (buffers : StepEntry.Buffers)
    (final : CSRun.Reference) (after : Heap) : Prop where
  stored : CSRun.Stored model.solve after (objects.instances.index slot.val) buffers final
  sourceEpoch : ∃! trajectory, CSRun.SourceEpoch source final trajectory
  sample : ∀ trajectory, CSRun.SourceEpoch source final trajectory →
    ∃ value : Binary64.Value, load after (StateProofs.stateAddress (objects.instances.index slot.val)) = some (.finite value) ∧
      |Binary64.value value - trajectory (Binary64.value final.current.time)| ≤
        (final.current.elapsed : ℝ) +
          |Binary64.value final.current.time - (Binary64.value final.start + (final.current.elapsed : ℝ))|
  readonly : CReadOnly.Preserves original after
  ownership : SlotOwners.Represents objects.flagsBlock after owners
  released : CSRun.Released objects program tag after slot owners owner final.mode
  frame : ∀ q, CSRun.Protected objects buffers q → CSRun.Outside (objects.instances.index slot.val) buffers q →
    Float64Access.Outside access q → q ≠ AtomicSlots.address objects.flagsBlock slot →
    CSRun.releasedHeap after objects slot final.mode q = original q

theorem RunOutcome.restored [CInterface]
    {objects : Objects} {program : Program Invocation} {tag : CAtomicBoolean.Calls.Event → Invocation}
    {slot : Fin objects.capacity} {owners : SlotOwners.State objects.capacity} {owner : Nat}
    (outcome : RunOutcome model objects program tag slot (SlotOwners.update owners slot (some owner)) owner
      original access buffers final after)
    (reserved : SlotOwners.reserve owners slot owner = some (SlotOwners.update owners slot (some owner))) :
    SlotOwners.release (SlotOwners.update owners slot (some owner)) slot owner = some owners ∧
    SlotOwners.Represents objects.flagsBlock (CSRun.releasedHeap after objects slot final.mode) owners := by
  have discharged := outcome.released.discharged
  have restored := outcome.released.ownersAfter
  rw [SlotOwners.release_reserved_restore reserved] at discharged restored
  exact ⟨discharged, restored⟩


/-- Access initialization supplies the same mutable CS trace and source records
as the full initialization protocol. Category inputs originate before creation. -/
def Continuation [CInterface] (model : Solve.FMI3Model source) (header : CFenv.Header) (objects : Objects)
    (program : Program Invocation) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (slot : Fin objects.capacity) (owners : SlotOwners.State objects.capacity) (owner : Nat)
    (original exited : Heap) (access : Float64Buffers.Layout) (buffers : StepEntry.Buffers)
    (initial final : CSRun.Reference) (actions : List CSMixedRun.Action) (statuses : List Int)
    (capability : Logging.Capability) (enabled : Bool) : Prop :=
  let p := objects.instances.index slot.val
  CSMixedRun.Trace header objects owners model.solve capability program p buffers exited enabled initial actions final statuses ∧
  (∀ observed events after, CSMixedRun.Completed program p exited actions observed events after →
    observed = statuses.map Value.integer ∧ capability.Configured after p ((CSMixedRun.loggingUpdate actions).getD enabled) ∧
    InitializationProtocol.Retention (CSMixedRun.loggingUpdate actions) p exited after ∧
    InitializationAccess.RunOutcome model objects program tag slot owners owner original access buffers final after) ∧
  (∀ observed events after records, CSMixedRun.Recorded program p exited actions observed events after records →
    CSMixedRun.SourceTrace source header p buffers exited initial actions observed records after final)

theorem Certificate.cs_continuation (header : CFenv.Header) (objects : Objects)
    (sigs : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap CLiteral.functionNames))
    (prepared : CSRunEnvironment.PreparedContract model sigs pool)
    (loggingPrepared : DebugLogging.PreparedContract model sigs pool)
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) (slot : Fin objects.capacity)
    (access : Float64Buffers.Layout) (buffers : StepEntry.Buffers) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation) (tag : CAtomicBoolean.Calls.Event → Invocation)
      (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
    program.internal = LiteralPreparation.program model sigs →
    program.externals "strcmp" = some (CStringCalls.compareExternal rfl) →
    program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
    program.externals "floor" = some (CMathCalls.floorExternal rfl) →
    ∀ (original live beforeEntry atExit : Heap) (state : ModelExchange.State) (args : Initialization.Arguments)
      (before during : List Float64Access.Request) (factoryArgs : FactoryArguments.Raw)
      (owners : SlotOwners.State objects.capacity) (owner : Nat),
    let p := objects.instances.index slot.val
    Certificate model program p access args .cs state Binary64.positiveZero live before during beforeEntry atExit →
    InstanceInitialization.Initialized live p .cs factoryArgs.environment factoryArgs.logger factoryArgs.logging →
    CReadOnly.Preserves (pool.install baseHeap firstBlock signed) original →
    CReadOnly.Preserves original live → CStorage.Preserves original live →
    (∀ q, ¬ p.InRecord q → q ≠ AtomicSlots.address objects.flagsBlock slot → live q = original q) →
    args.Admissible → StepArguments.Storage original p buffers →
    SlotOwners.Represents objects.flagsBlock live owners → owners slot = some owner →
    load live (p.member "slot") = some (.integer slot.val) →
    ∀ (capability : Logging.Capability) (actions : List CSMixedRun.Action) (final : CSRun.Reference) (statuses : List Int),
    capability.Describes factoryArgs → capability.Bound program →
    capability.Requires (fun _ effect => ∀ args before value after,
      effect.execute args before value after → CSRun.ProtectedFrame objects buffers before after) →
    CSMixedRun.ReferenceTrace header p buffers (runReference state args before during) actions final statuses →
    (∀ action ∈ actions, action.Prepared original) →
    (∀ action ∈ actions, capability.Requires (fun _ effect => ∀ args before value after,
      effect.execute args before value after → ∀ q, action.ReaderRegion q → after q = before q)) →
    (∀ action ∈ actions, ∀ q, action.ReaderRegion q → ¬ p.InRecord q ∧
      Float64Access.Outside access q ∧ CSRun.Outside p buffers q) →
    Continuation model header objects program tag slot owners owner original
      (InitializationBodies.exitHeap atExit p .cs) access buffers (runReference state args before during)
      final actions statuses capability factoryArgs.logging := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program tag range actual compare write rounding floorBound original live beforeEntry atExit state args before during factoryArgs
    owners owner
  let p := objects.instances.index slot.val
  dsimp only
  intro certified initialized literals liveReadonly liveStorage liveFrame admissible outputs represented owned metadata capability actions final statuses matching bound required admitted requests policies readerOutside
  obtain ⟨reset, enterDefined, exitDefined, termination, releaseDefined⟩ := prepared.execution header objects firstBlock program actual
  have releaseBindings : StaticRelease.Bindings program tag := ⟨releaseDefined, rfl, rfl, rfl, rfl, rfl, rfl, write⟩
  have finish := TerminationEnvironment.release_correct header objects (pool.addresses firstBlock) program tag termination releaseBindings
  let exited := InitializationBodies.exitHeap atExit p .cs
  have stored := certified.cs_run_storage admissible (outputs.storage_preserved liveStorage) initialized.storage.toStorage
  have readonly := liveReadonly.trans certified.readonly
  have poolFrame := literals.trans readonly
  have ownership := certified.owners represented
  have metadataAtExit := certified.metadata.trans metadata
  have finishRun (after : Heap) (finalStored : CSRun.Stored model.solve after p buffers final)
      (finalOwners : SlotOwners.Represents objects.flagsBlock after owners)
      (retained : InitializationProtocol.Retention (CSMixedRun.loggingUpdate actions) p exited after) (runReadonly : CReadOnly.Preserves exited after)
      (runFrame : ∀ q, CSRun.Protected objects buffers q → CSRun.Outside p buffers q → after q = exited q) :
      RunOutcome model objects program tag slot owners owner original access buffers final after := by
    have slotValue : load after (p.member "slot") = some (.integer slot.val) := by
      simpa only [load, retained.fields "slot" (by decide) (by decide)] using metadataAtExit
    have released := CSRun.finish_correct objects program tag finish releaseBindings rfl model.solve after slot buffers final owners owner
      finalStored (admitted.can_finish (Or.inl rfl)) finalOwners owned slotValue
    refine ⟨finalStored, CSRun.source_epoch model.solve final, fun _ epoch => finalStored.source_observation epoch,
      readonly.trans runReadonly, finalOwners, released, ?_⟩
    intro q guarded outside accessOutside notFlag
    have notState : q ≠ StateProofs.stateAddress p := by
      intro same
      exact outside.1 (same ▸ (p.member_in_record "model").member "x")
    exact (released.frame q (outside.field "mode") notFlag).trans
      ((runFrame q guarded outside).trans
        ((certified.frame q ⟨accessOutside, notState, fun name _ => outside.field name⟩).trans (liveFrame q outside.1 notFlag)))
  have originalConfig : capability.Configured live p factoryArgs.logging := by
    apply capability.initialized
    simpa only [matching.1, matching.2] using initialized
  have configured := certified.configuration originalConfig
  have writable := certified.retention.writable initialized.storage.logging
  have current : ∀ action ∈ actions, action.Prepared exited := by
    intro action member
    apply CSMixedRun.Action.Prepared.framed action (requests action member)
    intro q inside
    obtain ⟨notRecord, accessOutside, _⟩ := readerOutside action member q inside
    have field (name : String) : q ≠ p.member name := fun same => notRecord (same ▸ p.member_in_record name)
    have notState : q ≠ StateProofs.stateAddress p :=
      fun same => notRecord (same ▸ (p.member_in_record "model").member "x")
    have notFlag : q ≠ AtomicSlots.address objects.flagsBlock slot := by
      cases action with
      | run _ => cases inside
      | logging request =>
        have readable := (show request.Inputs original from requests (.logging request) member).load_ne_none inside
        intro same
        subst q
        exact readable (liveStorage.atomic_unreadable (represented slot) rfl)
    exact (certified.frame q ⟨accessOutside, notState, fun name _ => field name⟩).trans
      (liveFrame q notRecord notFlag)
  have trace := CSMixedRun.trace_correct header objects model sigs pool prepared.step loggingPrepared baseHeap firstBlock signed
    p buffers rfl program capability factoryArgs.logging range actual rounding floorBound compare bound required
    reset enterDefined exitDefined exited _ final actions statuses owners poolFrame stored configured writable ownership
    admitted current policies (fun action member q inside => (readerOutside action member q inside).2.2)
  refine ⟨trace, ?_, fun _ _ _ _ recorded => trace.recorded_source recorded⟩
  intro observed events after completed
  obtain ⟨statusValues, finalStored, finalConfig, retention, finalOwners, runReadonly, frame⟩ := trace.completed completed
  exact ⟨statusValues, finalConfig, retention, finishRun after finalStored finalOwners retention runReadonly frame⟩

end Rumoca.FMI3.InitializationAccess
end

noncomputable section
namespace Rumoca.FMI3.InitializationAccess
open CTree CMemory CLiteral CStringMemory StaticFactory Float64Access Float64Buffers CCalls.Events

/-- The actual source-bound factory and access initializer supply the mutable
CS continuation, using original category storage and the same prepared setter. -/
theorem runtime_create_cs_histories (compiled : compile input = .ok a)
    (build : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    Float64Metadata.Contract a.solve.prepareFMI3 metadata ∧
    Float64SetMetadata.Contract a.parsed.ast metadata ∧
    DebugLogging.MetadataContract metadata "logStatus" ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap CLiteral.functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      CSRunEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool ∧
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
        FactoryEntry.unsupported factoryArgs = false →
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
            slot owner .cs factoryArgs.environment factoryArgs.logger factoryArgs.logging ∧
          load live (StateProofs.stateAddress p) = some (.finite initial) ∧
          Binary64.value initial = (a.solve.initial.initial : ℝ) ∧
          CStorage.Preserves heap live ∧
          (∀ q, ¬ p.InRecord q → q ≠ AtomicSlots.address objects.flagsBlock slot → live q = heap q) ∧
          (∀ behavior, (machine program).Behaves
            (.calling (FactoryArguments.signature .cs).name (FactoryArguments.arguments .cs factoryArgs) heap .done) behavior ↔
            behavior = .terminates (trace.map tag) ⟨.pointer (some p), live⟩) ∧
          ∀ (buffers : Layout) (args : Initialization.Arguments) (before during : List Request),
          Stored heap buffers → buffers.Separate objects.instances → args.Admissible →
          (∀ request ∈ before, request.Fits buffers) → (∀ request ∈ before, request.StartQuery) →
          (∀ request ∈ during, request.Fits buffers) → (∀ request ∈ during, request.Allowed .cs .initialization) →
          ∃ beforeEntry atExit,
            Certificate a.solve.prepareFMI3 program p buffers args .cs ⟨initial⟩ Binary64.positiveZero
              live before during beforeEntry atExit ∧
            Executed program p buffers args live before during
              (expectedObservation a.solve.prepareFMI3 ⟨initial⟩ Binary64.positiveZero args before during)
              (InitializationBodies.exitHeap atExit p .cs) ∧
            InitializationCalls.SourceInitialized a.parsed.ast (InitializationBodies.exitHeap atExit p .cs) p args.start
              (trajectory ⟨initial⟩ args before during) ∧
            (∀ candidate, InitializationCalls.SourceInitialized a.parsed.ast (InitializationBodies.exitHeap atExit p .cs)
              p args.start candidate → candidate = trajectory ⟨initial⟩ args before during) ∧
            (∀ observation after, Executed program p buffers args live before during observation after ↔
              observation = expectedObservation a.solve.prepareFMI3 ⟨initial⟩ Binary64.positiveZero args before during ∧
              after = InitializationBodies.exitHeap atExit p .cs) ∧
            ∀ (stepBuffers : StepEntry.Buffers) (capability : Logging.Capability) (actions : List CSMixedRun.Action) (final : CSRun.Reference) (statuses : List Int)
              (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
              StepArguments.Storage heap objects.instances stepBuffers →
              capability.Describes factoryArgs → capability.Bound program →
              capability.Requires (fun _ effect => ∀ args before value after,
                effect.execute args before value after → CSRun.ProtectedFrame objects stepBuffers before after) →
              CSMixedRun.ReferenceTrace header objects.instances stepBuffers (runReference ⟨initial⟩ args before during)
                actions final statuses →
              program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
              program.externals "floor" = some (CMathCalls.floorExternal rfl) →
              (∀ action ∈ actions, action.Prepared heap) →
              (∀ action ∈ actions, capability.Requires (fun _ effect => ∀ args before value after,
                effect.execute args before value after → ∀ q, action.ReaderRegion q → after q = before q)) →
              (∀ action ∈ actions, ∀ q, action.ReaderRegion q → ¬ p.InRecord q ∧
                Float64Access.Outside buffers q ∧ CSRun.Outside p stepBuffers q) →
              Continuation a.solve.prepareFMI3 header objects program tag slot (SlotOwners.update owners slot (some owner)) owner
                heap (InitializationBodies.exitHeap atExit p .cs) buffers stepBuffers (runReference ⟨initial⟩ args before during)
                final actions statuses capability factoryArgs.logging := by
  obtain ⟨compiled, numerical, metadataVariables, writable, sigs, pool, made, printed, functions, prepared, _, _, _, loggingPrepared, create⟩ :=
    InitializationAccess.runtime_create_release compiled build
  refine ⟨compiled, numerical, metadataVariables, writable, DebugLogging.artifact_category _ _ build.metadata,
    sigs, pool, made, printed, functions, prepared, loggingPrepared, ?_⟩
  intro header instances flags separate baseHeap firstBlock signed
  let objects := StaticRuntime.objects instances flags separate
  let literals := pool.addresses firstBlock
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  dsimp only
  intro program tag actual identity exchange write factoryArgs heap literalFrame storage name supplied nameBytes tokenBytes
    supported nameBound tokenBound nameStored tokenStored fits accepted owners represented available owner
  obtain ⟨trace, slot, live, initial, work, reserved, created, loaded, agreement, preserved, createdFrame, creation, histories⟩ :=
    create Invocation header instances flags separate baseHeap firstBlock signed program tag actual identity exchange write
      .cs factoryArgs heap literalFrame storage name supplied nameBytes tokenBytes (Or.inr supported)
      nameBound tokenBound nameStored tokenStored fits accepted owners represented available owner
  let p := objects.instances.index slot.val
  refine ⟨trace, slot, live, initial, work, reserved, created, loaded, agreement, preserved, createdFrame, creation, ?_⟩
  intro buffers args before during buffersStored buffersSeparate admissible beforeFits beforeAllowed duringFits duringAllowed
  obtain ⟨beforeEntry, atExit, certified, executed, _⟩ := histories buffers args before during buffersStored buffersSeparate
    admissible beforeFits beforeAllowed duringFits duringAllowed
  obtain ⟨_, initialized, uniqueSource⟩ := certified.completed_source executed
  refine ⟨beforeEntry, atExit, certified, executed, initialized, uniqueSource, fun _ _ => certified.execution_iff, ?_⟩
  intro stepBuffers capability actions final statuses range outputs matching bound required admitted rounding floorBound requests policies readerOutside
  exact Certificate.cs_continuation header objects sigs pool prepared loggingPrepared baseHeap firstBlock signed slot buffers stepBuffers
    program tag range actual identity.compareBinding write rounding floorBound heap live beforeEntry atExit ⟨initial⟩ args before during factoryArgs
      (SlotOwners.update owners slot (some owner)) owner certified created.initialized literalFrame
      (termination_preserves ((creation _).mpr rfl)) preserved createdFrame admissible (outputs.at_index slot.val)
      created.represented created.owned created.metadata capability actions final statuses matching bound required
      (admitted.rehandle p) requests policies readerOutside

end Rumoca.FMI3.InitializationAccess
end
