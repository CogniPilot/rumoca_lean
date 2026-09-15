import Rumoca.FMI3CreatedInitializationProtocol
import Rumoca.FMI3CSMixedRun
import RumocaFMI3.CSMixedLifecycle
import RumocaFMI3.LoggingCapabilityCreation
import RumocaFMI3.InitializationProtocolRunFrames

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CMemory StaticFactory CCalls.Events
variable {source : AST.Model} {model : Solve.FMI3Model source}

structure CSRunOutcome [CInterface] (model : Solve.FMI3Model source) (objects : Objects)
    (program : Program Invocation) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (slot : Fin objects.capacity) (owners : SlotOwners.State objects.capacity) (owner : Nat)
    (original : Heap) (access : Float64Buffers.Layout) (initialization : List Action)
    (buffers : StepEntry.Buffers) (final : CSRun.Reference) (after : Heap) : Prop where
  stored : CSRun.Stored model.solve after (objects.instances.index slot.val) buffers final
  sourceEpoch : ∃! trajectory, CSRun.SourceEpoch source final trajectory
  sample : ∀ trajectory, CSRun.SourceEpoch source final trajectory →
    ∃ value : Binary64.Value,
      load after (StateProofs.stateAddress (objects.instances.index slot.val)) = some (.finite value) ∧
      |Binary64.value value - trajectory (Binary64.value final.current.time)| ≤
        (final.current.elapsed : ℝ) +
          |Binary64.value final.current.time - (Binary64.value final.start + (final.current.elapsed : ℝ))|
  readonly : CReadOnly.Preserves original after
  ownership : SlotOwners.Represents objects.flagsBlock after (SlotOwners.update owners slot (some owner))
  released : CSRun.Released objects program tag after slot (SlotOwners.update owners slot (some owner)) owner final.mode
  discharged : SlotOwners.release (SlotOwners.update owners slot (some owner)) slot owner = some owners
  restored : SlotOwners.Represents objects.flagsBlock (CSRun.releasedHeap after objects slot final.mode) owners
  frame : ∀ q, CSRun.Protected objects buffers q →
    CSRun.Outside (objects.instances.index slot.val) buffers q →
    Untouched (objects.instances.index slot.val) access initialization q →
    q ≠ AtomicSlots.address objects.flagsBlock slot →
    CSRun.releasedHeap after objects slot final.mode q = original q


/-- One capability supplies every current logging view. The raw history and
its source records retain all actual returns and callback alternatives. -/
def CSContinuation [CInterface] (model : Solve.FMI3Model source) (header : CFenv.Header) (objects : Objects)
    (program : Program Invocation) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (slot : Fin objects.capacity) (owners : SlotOwners.State objects.capacity) (owner : Nat)
    (original exited : Heap) (access : Float64Buffers.Layout) (initialization : List InitializationProtocol.Action)
    (buffers : StepEntry.Buffers) (initial final : CSRun.Reference)
    (actions : List CSMixedRun.Action) (statuses : List Int) (capability : Logging.Capability) (enabled : Bool) : Prop :=
  let p := objects.instances.index slot.val
  CSMixedRun.Trace header objects (SlotOwners.update owners slot (some owner)) model.solve capability
    program p buffers exited enabled initial actions final statuses ∧
  (∀ observed events after, CSMixedRun.Completed program p exited actions observed events after →
    observed = statuses.map Value.integer ∧ capability.Configured after p ((CSMixedRun.loggingUpdate actions).getD enabled) ∧
    InitializationProtocol.Retention (CSMixedRun.loggingUpdate actions) p exited after ∧
    InitializationProtocol.CSRunOutcome model objects program tag slot owners owner original access initialization buffers final after) ∧
  (∀ observed events after records, CSMixedRun.Recorded program p exited actions observed events after records →
    CSMixedRun.SourceTrace source header p buffers exited initial actions observed records after final)

theorem CreatedSourceContract.cs_continuation (header : CFenv.Header) (objects : Objects)
    (sigs : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap CLiteral.functionNames))
    (prepared : CSRunEnvironment.PreparedContract model sigs pool)
    (loggingPrepared : DebugLogging.PreparedContract model sigs pool)
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation) (tag : CAtomicBoolean.Calls.Event → Invocation)
      (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
      program.internal = LiteralPreparation.program model sigs →
      program.externals "strcmp" = some (CStringCalls.compareExternal rfl) →
      program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
      program.externals "floor" = some (CMathCalls.floorExternal rfl) →
    ∀ (owners : SlotOwners.State objects.capacity) (slot : Fin objects.capacity) (owner : Nat)
      (retained : Address → Prop) (original live exited : Heap) (access : Float64Buffers.Layout)
      (factoryArgs : FactoryArguments.Raw) (initialization : List Action) (state : State)
      (initObserved : List (Float64Access.Observation Invocation)) (initCheckpoints : List Heap)
      (args : Initialization.Arguments) (buffers : StepEntry.Buffers) (readers : ReadBank),
      let p := objects.instances.index slot.val
      CreatedSourceContract model program objects tag retained owners slot owner original
        (pool.install baseHeap firstBlock signed) live access .cs initialization state readers →
      Created live objects.instances objects.flagsBlock (SlotOwners.update owners slot (some owner)) slot owner .cs
        factoryArgs.environment factoryArgs.logger factoryArgs.logging →
      SlotOwners.reserve owners slot owner = some (SlotOwners.update owners slot (some owner)) →
      (∀ q, ¬ p.InRecord q → q ≠ AtomicSlots.address objects.flagsBlock slot → live q = original q) →
      Completed program p access live initialization initObserved exited initCheckpoints →
      state.phase = .initialized args → StepArguments.Storage original p buffers →
      CSOutputsGuarded objects retained buffers →
    ∀ (capability : Logging.Capability) (actions : List CSMixedRun.Action) (final : CSRun.Reference) (statuses : List Int),
      capability.Describes factoryArgs → capability.Bound program →
      capability.Requires (fun _ effect => ∀ args before value after,
        effect.execute args before value after → CSRun.ProtectedFrame objects buffers before after) →
      CSMixedRun.ReferenceTrace header p buffers (csReference state args) actions final statuses →
      (∀ action ∈ actions, action.Prepared original) →
      (∀ action ∈ actions, ∀ q, action.ReaderRegion q → readers.Region q) →
      (∀ action ∈ actions, capability.Requires (fun _ effect => ∀ args before value after,
        effect.execute args before value after → ∀ q, action.ReaderRegion q → after q = before q)) →
      (∀ action ∈ actions, ∀ q, action.ReaderRegion q → CSRun.Outside p buffers q) →
      CSContinuation model header objects program tag slot owners owner original exited access initialization buffers
        (csReference state args) final actions statuses capability ((loggingUpdate initialization).getD factoryArgs.logging) := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program tag range actual compare write rounding floorBound owners slot owner retained original live exited access factoryArgs
    initialization state initObserved initCheckpoints args buffers readers
  let p := objects.instances.index slot.val
  dsimp only
  intro initialized created reserved creationFrame executed phase outputs guarded capability actions final statuses matching bound required admitted requests included policies readerOutside
  obtain ⟨_, _, invariant, _, keeps, initialFrame⟩ := initialized.initialized.completed _ _ _ executed
  have readonly := (initialized.completed _ _ _ executed).1
  have stored := invariant.cs_ready model.solve phase outputs guarded
  obtain ⟨reset, enterDefined, exitDefined, termination, releaseDefined⟩ :=
    prepared.execution header objects firstBlock program actual
  have releaseBindings : StaticRelease.Bindings program tag := ⟨releaseDefined, rfl, rfl, rfl, rfl, rfl, rfl, write⟩
  have finish := TerminationEnvironment.release_correct header objects (pool.addresses firstBlock) program tag termination releaseBindings
  have metadataAtExit : load exited (p.member "slot") = some (.integer slot.val) := by
    change load exited ((objects.instances.index slot.val).member "slot") = _
    simpa only [load, keeps.fields "slot" (by decide) (by decide)] using created.metadata
  have finishRun (after : Heap) (finalStored : CSRun.Stored model.solve after p buffers final)
      (finalOwners : SlotOwners.Represents objects.flagsBlock after (SlotOwners.update owners slot (some owner)))
      (retains : InitializationProtocol.Retention (CSMixedRun.loggingUpdate actions) p exited after) (runReadonly : CReadOnly.Preserves exited after)
      (runFrame : ∀ q, CSRun.Protected objects buffers q → CSRun.Outside p buffers q → after q = exited q) :
      CSRunOutcome model objects program tag slot owners owner original access initialization buffers final after := by
    have slotValue : load after (p.member "slot") = some (.integer slot.val) := by
      simpa only [load, retains.fields "slot" (by decide) (by decide)] using metadataAtExit
    have released := CSRun.finish_correct objects program tag finish releaseBindings rfl model.solve after slot buffers final
      (SlotOwners.update owners slot (some owner)) owner finalStored (admitted.can_finish (Or.inl rfl)) finalOwners
      (by simp [SlotOwners.update]) slotValue
    have discharged := released.discharged
    have restored := released.ownersAfter
    rw [SlotOwners.release_reserved_restore reserved] at discharged restored
    refine ⟨finalStored, CSRun.source_epoch model.solve final, fun _ epoch => finalStored.source_observation epoch,
      readonly.trans runReadonly, finalOwners, released, discharged, restored, ?_⟩
    intro q protectedOutput outside untouched notFlag
    exact (released.frame q (outside.field "mode") notFlag).trans ((runFrame q protectedOutput outside).trans
      ((initialFrame q (guarded.protects protectedOutput) untouched).trans (creationFrame q untouched.1 notFlag)))
  have configured := keeps.configured (Logging.Capability.created matching created)
  have writable := keeps.writable created.initialized.storage.logging
  have current : ∀ action ∈ actions, action.Prepared exited := by
    intro action member
    exact CSMixedRun.Action.Prepared.framed action (requests action member)
      (fun q inside => invariant.readerFrame q (included action member q inside))
  have certified := CSMixedRun.trace_correct header objects model sigs pool prepared.step loggingPrepared baseHeap firstBlock signed
    p buffers rfl program capability ((loggingUpdate initialization).getD factoryArgs.logging)
    range actual rounding floorBound compare bound required reset enterDefined exitDefined
    exited _ final actions statuses (SlotOwners.update owners slot (some owner)) invariant.readonly stored
    configured writable invariant.ownership admitted current policies readerOutside
  refine ⟨certified, ?_, fun _ _ _ _ recorded => certified.recorded_source recorded⟩
  intro observed events after completed
  obtain ⟨statusValues, finalStored, finalConfig, retention, finalOwners, runReadonly, frame⟩ := certified.completed completed
  exact ⟨statusValues, finalConfig, retention, finishRun after finalStored finalOwners retention runReadonly frame⟩

end Rumoca.FMI3.InitializationProtocol
end
