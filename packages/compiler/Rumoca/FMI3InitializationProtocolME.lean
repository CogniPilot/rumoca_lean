import Rumoca.FMI3CreatedInitializationProtocol
import Rumoca.FMI3MEMixedRun
import RumocaFMI3.InitializationProtocolRunFrames
import RumocaFMI3.LoggingCapabilityCreation

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CMemory StaticFactory CCalls.Events

/-- Simulation uses the existing mixed ME relation. The additional frame
records all initialization-access buffers, including rejected raw transfers. -/
structure MEContinuation [CInterface] (model : Solve.Model source) (objects : Objects)
    (program : Program Invocation) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (slot : Fin objects.capacity) (owners : SlotOwners.State objects.capacity) (owner : Nat)
    (original exited : Heap) (access : Float64Buffers.Layout) (initialization : List Action)
    (addresses : String → Address) (buffer : Address)
    (initial final : MENumericalHistory.ReferenceState) (clock finalClock : Time.Clock)
    (actions : List MEMixedRun.Action) (capability : Logging.Capability) (enabled : Bool) : Prop where
  trace : MEMixedRun.Trace model.prepareFMI3 objects (SlotOwners.update owners slot (some owner)) capability program
    (objects.instances.index slot.val) addresses buffer exited enabled initial clock actions final finalClock
  completed : ∀ observed after epochs,
    MEMixedRun.Completed program (objects.instances.index slot.val) addresses buffer exited actions observed after epochs →
    MENumericalHistory.Stored after (objects.instances.index slot.val) finalClock final addresses buffer ∧
    Reset.Storage after (objects.instances.index slot.val) ∧
    capability.Configured after (objects.instances.index slot.val) ((MEMixedRun.loggingUpdate actions).getD enabled) ∧
    Retention (MEMixedRun.loggingUpdate actions) (objects.instances.index slot.val) exited after ∧
    MEMixedRun.SourceObservations model actions observed ∧
    MENumericalRun.InitializedEpochs source (objects.instances.index slot.val) epochs ∧
    CReadOnly.Preserves original after ∧
    LifecycleRelease.Released objects program tag after slot (SlotOwners.update owners slot (some owner)) owner .me final.control.mode ∧
    SlotOwners.release (SlotOwners.update owners slot (some owner)) slot owner = some owners ∧
    SlotOwners.Represents objects.flagsBlock (LifecycleRelease.releasedHeap after objects slot final.control.mode) owners ∧
    ∀ q, MEFailure.Protected objects addresses buffer q →
      Untouched (objects.instances.index slot.val) access initialization q →
      MENumericalRun.Outside (objects.instances.index slot.val) addresses buffer q →
      q ≠ AtomicSlots.address objects.flagsBlock slot →
      LifecycleRelease.releasedHeap after objects slot final.control.mode q = original q

theorem CreatedSourceContract.me_continuation {source : AST.Model} (model : Solve.Model source)
    (header : CFenv.Header) (objects : Objects) (sigs : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model.prepareFMI3 sigs).flatMap CLiteral.functionNames))
    (lifecycle : LifecycleEnvironment.PreparedContract model.prepareFMI3 sigs)
    (prepared : MEEnvironment.PreparedContract model.prepareFMI3 sigs pool)
    (counts : ∀ events, CountEnvironment.PreparedContract model.prepareFMI3 sigs events pool)
    (nominals : NominalEnvironment.PreparedContract model.prepareFMI3 sigs pool)
    (loggingPrepared : DebugLogging.PreparedContract model.prepareFMI3 sigs pool)
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation) (tag : CAtomicBoolean.Calls.Event → Invocation),
      program.internal = LiteralPreparation.program model.prepareFMI3 sigs →
      program.externals "strcmp" = some (CStringCalls.compareExternal (by rfl)) →
      program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
    ∀ (owners : SlotOwners.State objects.capacity) (slot : Fin objects.capacity) (owner : Nat)
      (retained : Address → Prop) (original live exited : Heap) (access : Float64Buffers.Layout)
      (factoryArgs : FactoryArguments.Raw) (initialization : List Action) (state : State)
      (initObserved : List (Float64Access.Observation Invocation)) (initCheckpoints : List Heap)
      (args : Initialization.Arguments) (addresses : String → Address) (buffer : Address) (readers : ReadBank),
      let p := objects.instances.index slot.val
      CreatedSourceContract model.prepareFMI3 program objects tag retained owners slot owner original
        (pool.install baseHeap firstBlock signed) live access .me initialization state readers →
      Created live objects.instances objects.flagsBlock (SlotOwners.update owners slot (some owner)) slot owner .me
        factoryArgs.environment factoryArgs.logger factoryArgs.logging →
      SlotOwners.reserve owners slot owner = some (SlotOwners.update owners slot (some owner)) →
      (∀ q, ¬ p.InRecord q → q ≠ AtomicSlots.address objects.flagsBlock slot → live q = original q) →
      Completed program p access live initialization initObserved exited initCheckpoints →
      state.phase = .initialized args → MENumericalHistory.CallerStorage original p addresses buffer →
      MEOutputsGuarded objects retained addresses buffer →
    ∀ (capability : Logging.Capability) (actions : List MEMixedRun.Action)
      (final : MENumericalHistory.ReferenceState) (finalClock : Time.Clock),
      capability.Describes factoryArgs → capability.Bound program →
      capability.Requires (fun _ effect => MEFailure.Respects effect objects addresses buffer) →
      MEMixedRun.ReferenceTrace buffer (meReference state args) (Time.Clock.initial args.start) actions final finalClock →
      (∀ action ∈ actions, action.Prepared objects original addresses buffer) →
      (∀ action ∈ actions, ∀ q, action.CallerRegion q → Float64Rejection.Protected objects retained q) →
      (∀ action ∈ actions, capability.Requires (fun _ effect => ∀ args before value after,
        effect.execute args before value after → CStorage.PreservesOn action.CallerRegion before after)) →
      (∀ action ∈ actions, capability.Requires (fun _ effect => ∀ args before value after,
        effect.execute args before value after → ∀ q, action.ReaderRegion q → after q = before q)) →
      (∀ action ∈ actions, ∀ q, action.ReaderRegion q → readers.Region q) →
      (∀ action ∈ actions, ∀ q, action.ReaderRegion q → MENumericalRun.Outside p addresses buffer q ∧ q ≠ p.member "logging") →
      (∀ writer ∈ actions, ∀ reader ∈ actions, ∀ q, reader.ReaderRegion q → ¬ writer.CallerRegion q) →
      MEContinuation model objects program tag slot owners owner original exited access initialization addresses buffer
        (meReference state args) final (Time.Clock.initial args.start) finalClock actions capability ((loggingUpdate initialization).getD factoryArgs.logging) := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program tag actual compare write owners slot owner retained original live exited access factoryArgs initialization state
    initObserved initCheckpoints args addresses buffer readers
  let p := objects.instances.index slot.val
  dsimp only
  intro initialized created reserved creationFrame executed phase outputs guarded capability actions final finalClock matching bound required admitted requests regions policies readPolicies included readerOutside separateReaders
  obtain ⟨_, _, invariant, _, keeps, initialFrame⟩ := initialized.initialized.completed _ _ _ executed
  have readonly := (initialized.completed _ _ _ executed).1
  have stored := invariant.me_ready phase outputs guarded
  have configured := keeps.configured (Logging.Capability.created matching created)
  have writable := keeps.writable created.initialized.storage.logging
  obtain ⟨reset, enterDefined, exitDefined, termination, releaseDefined⟩ :=
    lifecycle.execution header objects (pool.addresses firstBlock) program actual
  have releaseBindings : StaticRelease.Bindings program tag := ⟨releaseDefined, rfl, rfl, rfl, rfl, rfl, rfl, write⟩
  have finish := TerminationEnvironment.release_correct header objects (pool.addresses firstBlock) program tag termination releaseBindings
  have current : ∀ action ∈ actions, action.Prepared objects exited addresses buffer := by
    intro action member
    exact MEMixedRun.Action.Prepared.preserved action (requests action member)
      (fun q inside => invariant.caller q (regions action member q inside))
      (fun q inside => invariant.readerFrame q (included action member q inside))
  have certified := MEMixedRun.trace_correct header objects model.prepareFMI3 sigs pool prepared counts nominals loggingPrepared baseHeap firstBlock signed
    program capability ((loggingUpdate initialization).getD factoryArgs.logging) actual compare bound reset enterDefined exitDefined exited p _ _ final finalClock addresses buffer actions
      (SlotOwners.update owners slot (some owner)) required configured writable rfl invariant.ownership invariant.readonly
      stored invariant.stored.reset admitted current policies readPolicies readerOutside separateReaders
  refine ⟨certified, ?_⟩
  intro observed after epochs completed
  obtain ⟨finalStored, finalReset, finalConfig, retention, finalOwners, runReadonly, frame⟩ := certified.completed completed
  obtain ⟨sourceValues, sourceEpochs⟩ := certified.source model completed
  have metadataAtExit : load exited (p.member "slot") = some (.integer slot.val) := by
    change load exited ((objects.instances.index slot.val).member "slot") = _
    simpa only [load, keeps.fields "slot" (by decide) (by decide)] using created.metadata
  have metadataAfter := (certified.slot stored rfl completed).trans metadataAtExit
  have released := LifecycleRelease.finish_correct objects program tag finish releaseBindings rfl after slot .me
    final.control.mode (SlotOwners.update owners slot (some owner)) owner finalStored.control.kind finalStored.control.mode
      (admitted.can_finish (Or.inl (by simp [meReference, MENumericalHistory.ReferenceState.initial,
        MEHistory.ReferenceState.initial, Reference.Allowed]))) finalOwners (by simp [SlotOwners.update]) metadataAfter
  have discharged := released.discharged
  have restored := released.ownersAfter
  rw [SlotOwners.release_reserved_restore reserved] at discharged restored
  refine ⟨finalStored, finalReset, finalConfig, retention, sourceValues, sourceEpochs, readonly.trans runReadonly,
    released, discharged, restored, ?_⟩
  intro q protectedOutput untouched outside notFlag
  have notMode : q ≠ p.member "mode" := fun same => untouched.1 (same ▸ p.member_in_record "mode")
  exact (released.frame q notMode notFlag).trans ((frame q protectedOutput outside (fun same => untouched.1 (same ▸ p.member_in_record "logging"))).trans
    ((initialFrame q (guarded.protects protectedOutput) untouched).trans (creationFrame q untouched.1 notFlag)))

end Rumoca.FMI3.InitializationProtocol
end
