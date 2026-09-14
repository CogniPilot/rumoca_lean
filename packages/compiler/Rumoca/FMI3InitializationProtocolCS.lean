import Rumoca.FMI3CreatedInitializationProtocol
import Rumoca.FMI3CSRunLogging
import RumocaFMI3.CSRunFinish
import RumocaFMI3.CSRunCompleted
import RumocaFMI3.InitializationProtocolRunFrames

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CMemory StaticFactory CCalls.Events

variable {source : AST.Model} {model : Solve.FMI3Model source}

/-- The completed CS run is tied to the original allocation and to the
initialization history that established its seed. -/
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

/-- Suppressed and enabled logging share the same actual initialized heap.
Callback return values and final heaps are universally quantified. -/
def CSContinuation [CInterface] (model : Solve.FMI3Model source) (objects : Objects)
    (program : Program Invocation) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (slot : Fin objects.capacity) (owners : SlotOwners.State objects.capacity) (owner : Nat)
    (original exited : Heap) (access : Float64Buffers.Layout) (initialization : List Action)
    (buffers : StepEntry.Buffers) (initial final : CSRun.Reference)
    (actions : List CSRun.Action) (statuses : List Int) (factoryArgs : FactoryArguments.Raw) : Prop :=
  let p := objects.instances.index slot.val
  ((factoryArgs.logger = none ∨ factoryArgs.logging = false) →
    ∃ after, CSRun.Calls model.solve program p buffers exited initial actions after final statuses ∧
      CSRun.Completed program p exited actions statuses [] after ∧
      ∀ observed events actualAfter, CSRun.Completed program p exited actions observed events actualAfter →
        observed = statuses ∧ events = [] ∧
          CSRunOutcome model objects program tag slot owners owner original access initialization buffers final actualAfter) ∧
  (∀ logger : CSRun.Logger, factoryArgs.logger = some logger.pointer → factoryArgs.logging = true →
    factoryArgs.environment = logger.environment → logger.Bound program → logger.Respects objects buffers →
    CSRun.LoggedTrace objects logger (SlotOwners.update owners slot (some owner)) model.solve program p buffers
      exited initial actions final statuses ∧
    ∀ observed events after, CSRun.Completed program p exited actions observed events after →
      observed = statuses ∧ CSRunOutcome model objects program tag slot owners owner original access initialization buffers final after)

theorem CreatedSourceContract.cs_continuation (header : CFenv.Header) (objects : Objects)
    (sigs : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap CLiteral.functionNames))
    (prepared : CSRunEnvironment.PreparedContract model sigs pool)
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation) (tag : CAtomicBoolean.Calls.Event → Invocation)
      (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
      program.internal = LiteralPreparation.program model sigs →
      program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
      program.externals "floor" = some (CMathCalls.floorExternal rfl) →
    ∀ (owners : SlotOwners.State objects.capacity) (slot : Fin objects.capacity) (owner : Nat)
      (retained : Address → Prop) (original live exited : Heap) (access : Float64Buffers.Layout)
      (factoryArgs : FactoryArguments.Raw) (initialization : List Action) (state : State)
      (initObserved : List (Float64Access.Observation Invocation)) (initCheckpoints : List Heap)
      (args : Initialization.Arguments) (buffers : StepEntry.Buffers),
      let p := objects.instances.index slot.val
      CreatedSourceContract model program objects tag retained owners slot owner original
        (pool.install baseHeap firstBlock signed) live access .cs initialization state →
      Created live objects.instances objects.flagsBlock (SlotOwners.update owners slot (some owner)) slot owner .cs
        factoryArgs.environment factoryArgs.logger factoryArgs.logging →
      SlotOwners.reserve owners slot owner = some (SlotOwners.update owners slot (some owner)) →
      (∀ q, ¬ p.InRecord q → q ≠ AtomicSlots.address objects.flagsBlock slot → live q = original q) →
      Completed program p access live initialization initObserved exited initCheckpoints →
      state.phase = .initialized args → StepArguments.Storage original p buffers →
      CSOutputsGuarded objects retained buffers →
    ∀ (actions : List CSRun.Action) (final : CSRun.Reference) (statuses : List Int),
      CSRun.ReferenceTrace header p buffers (csReference state args) actions final statuses →
      CSContinuation model objects program tag slot owners owner original exited access initialization buffers
        (csReference state args) final actions statuses factoryArgs := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program tag range actual write rounding floorBound owners slot owner retained original live exited access factoryArgs
    initialization state initObserved initCheckpoints args buffers
  let p := objects.instances.index slot.val
  dsimp only
  intro initialized created reserved creationFrame executed phase outputs guarded actions final statuses admitted
  obtain ⟨_, _, invariant, _, keeps, initialFrame⟩ := initialized.initialized.completed _ _ _ executed
  have readonly := (initialized.completed _ _ _ executed).1
  have stored := invariant.cs_ready model.solve phase outputs guarded
  obtain ⟨reset, enterDefined, exitDefined, termination, releaseDefined⟩ :=
    prepared.execution header objects firstBlock program actual
  have releaseBindings : StaticRelease.Bindings program tag := ⟨releaseDefined, rfl, rfl, rfl, rfl, rfl, rfl, write⟩
  have finish := TerminationEnvironment.release_correct header objects (pool.addresses firstBlock) program tag termination releaseBindings
  have metadataAtExit : load exited (p.member "slot") = some (.integer slot.val) := by
    change load exited ((objects.instances.index slot.val).member "slot") = _
    simpa only [load, keeps "slot" (by decide)] using created.metadata
  have finishRun (after : Heap) (finalStored : CSRun.Stored model.solve after p buffers final)
      (finalOwners : SlotOwners.Represents objects.flagsBlock after (SlotOwners.update owners slot (some owner)))
      (retains : CSRun.Retains p exited after) (runReadonly : CReadOnly.Preserves exited after)
      (runFrame : ∀ q, CSRun.Protected objects buffers q → CSRun.Outside p buffers q → after q = exited q) :
      CSRunOutcome model objects program tag slot owners owner original access initialization buffers final after := by
    have slotValue : load after (p.member "slot") = some (.integer slot.val) := by
      simpa only [load, retains "slot" (by simp)] using metadataAtExit
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
  constructor
  · intro suppressed
    have quiet : CSRun.Suppressed live p :=
      ⟨factoryArgs.logger, factoryArgs.logging, created.initialized.loggerValue, created.initialized.loggingValue, suppressed⟩
    obtain ⟨after, calls, finalStored, retains, runReadonly, atomic, frame⟩ :=
      CSRun.trace_framed header objects model sigs pool prepared.step baseHeap firstBlock signed p buffers
        program range actual rounding floorBound reset enterDefined exitDefined exited _ final actions statuses
        invariant.readonly stored (keeps.cs.suppressed quiet) admitted
    refine ⟨after, calls, calls.executes, ?_⟩
    intro observed events actualAfter completed
    obtain ⟨statusesMatch, eventsMatch, same⟩ := calls.determines completed
    subst actualAfter
    exact ⟨statusesMatch, eventsMatch, finishRun after finalStored
      (SlotOwners.ordinary_preserves invariant.ownership atomic) retains runReadonly (fun q _ => frame q)⟩
  · intro logger loggerArg loggingArg environmentArg bound policy
    have logging : logger.Stored live p :=
      ⟨by simpa only [loggerArg] using created.initialized.loggerValue,
        by simpa only [loggingArg, CBody.boolean] using created.initialized.loggingValue,
        by simpa only [environmentArg] using created.initialized.environmentValue⟩
    have trace := CSRun.logged_trace_correct header objects model sigs pool prepared.step baseHeap firstBlock signed
      p buffers rfl program range logger actual rounding floorBound bound policy reset enterDefined exitDefined
      exited _ final actions statuses (SlotOwners.update owners slot (some owner)) invariant.readonly stored
      (keeps.cs.logger logging) invariant.ownership admitted
    refine ⟨trace, ?_⟩
    intro observed events after completed
    have statusesMatch := trace.statuses_eq completed
    subst observed
    obtain ⟨finalStored, _, finalOwners, retains, runReadonly, frame⟩ := trace.completed completed
    exact ⟨rfl, finishRun after finalStored finalOwners retains runReadonly frame⟩

end Rumoca.FMI3.InitializationProtocol
end
