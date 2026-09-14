import RumocaFMI3.MEProtocolInterrupted
import Rumoca.FMI3MEProtocolPrefixes

noncomputable section
namespace Rumoca.FMI3.MEProtocol
open CMemory StaticFactory CCalls.Events
open InitializationProtocol (Invariant Persistent MEExecution SourceContract)

variable {source : AST.Model} {model : Solve.Model source}

structure InitializationEvidence (model : Solve.Model source) (p : Address)
    (actions : List InitializationProtocol.Action) (observed : List (Float64Access.Observation Invocation))
    (checkpoints : List Heap) : Prop where
  observations : InitializationProtocol.Observed model.prepareFMI3 .reset actions observed
  sourceIVPs : List.Forall₂ (InitializationProtocol.SourceCheckpoint source p)
    (InitializationProtocol.exitStates .reset actions) checkpoints

structure CycleEvidence (model : Solve.Model source) (p : Address) (cycle : Cycle)
    (initial : List (Float64Access.Observation Invocation)) (checkpoints : List Heap)
    (observed : List (MENumericalHistory.Observation Invocation)) (epochs : List MENumericalRun.Epoch) : Prop where
  initialization : InitializationEvidence model p cycle.initialization initial checkpoints
  observations : MEMixedRun.SourceObservations source cycle.simulation observed
  sourceEpochs : MENumericalRun.InitializedEpochs source p epochs

/-- All completed initialization and ME observations survive later resets.
The numerical claims concern derivatives and initialized IVPs, not the
correctness of the importer's integration algorithm. -/
inductive SourceTrace (model : Solve.Model source) (p : Address) : Plan → List Record → Prop where
  | finish : InitializationEvidence model p actions observed checkpoints →
      SourceTrace model p (.finish actions state) [.initialization observed checkpoints after]
  | last : CycleEvidence model p cycle initial checkpoints observed epochs →
      SourceTrace model p (.last cycle)
        [.initialization initial checkpoints exited, .simulation observed epochs after]
  | next : CycleEvidence model p cycle initial checkpoints observed epochs →
      SourceTrace model p following records →
      SourceTrace model p (.next cycle following)
        (.initialization initial checkpoints exited :: .simulation observed epochs simulated ::
          .reset [] (.integer 0) (Reset.finalHeap simulated p) :: records)

inductive SourceInterrupted (model : Solve.Model source) (p : Address)
    (addresses : String → Address) (buffer : Address) : Plan → List Record → StopRecord → Prop where
  | finish : InitializationProtocol.SourcePrefix model.prepareFMI3 p .me .reset actions stop →
      SourceInterrupted model p addresses buffer (.finish actions state) [] (.initialization stop)
  | lastInitialization : InitializationProtocol.SourcePrefix model.prepareFMI3 p .me .reset cycle.initialization stop →
      SourceInterrupted model p addresses buffer (.last cycle) [] (.initialization stop)
  | nextInitialization : InitializationProtocol.SourcePrefix model.prepareFMI3 p .me .reset cycle.initialization stop →
      SourceInterrupted model p addresses buffer (.next cycle following) [] (.initialization stop)
  | lastSimulation : InitializationEvidence model p cycle.initialization initial checkpoints →
      MEMixedRun.SourcePrefix source p addresses buffer (InitializationProtocol.meReference cycle.state cycle.args)
        (Time.Clock.initial cycle.args.start) cycle.simulation stop →
      SourceInterrupted model p addresses buffer (.last cycle)
        [.initialization initial checkpoints exited] (.simulation stop)
  | nextSimulation : InitializationEvidence model p cycle.initialization initial checkpoints →
      MEMixedRun.SourcePrefix source p addresses buffer (InitializationProtocol.meReference cycle.state cycle.args)
        (Time.Clock.initial cycle.args.start) cycle.simulation stop →
      SourceInterrupted model p addresses buffer (.next cycle following)
        [.initialization initial checkpoints exited] (.simulation stop)
  | later : CycleEvidence model p cycle initial checkpoints observed epochs →
      SourceInterrupted model p addresses buffer following records stop →
      SourceInterrupted model p addresses buffer (.next cycle following)
        (.initialization initial checkpoints exited :: .simulation observed epochs simulated ::
          .reset [] (.integer 0) (Reset.finalHeap simulated p) :: records) stop

structure Ready [CInterface] (program : Program Invocation) (objects : Objects) (retained : Address → Prop)
    (owners : SlotOwners.State objects.capacity) (original literals heap : Heap) (p : Address) (mode : Mode) : Prop where
  kindValue : load heap (p.member "kind") = some (.integer Kind.me.code)
  modeValue : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩
  finishable : LifecycleRelease.CanFinish .me mode
  persistent : Persistent program objects retained owners original literals heap p

variable [interface : CInterface] {program : Program Invocation} {objects : Objects}
  {owners : SlotOwners.State objects.capacity}

theorem Ready.initialization
    (invariant : Invariant program objects retained owners original literals heap p .me state)
    (finished : state.phase.Finished) : Ready program objects retained owners original literals heap p (state.phase.mode .me) :=
  ⟨invariant.stored.instanceStored.kind, invariant.stored.instanceStored.mode,
    state.phase.can_finish .me finished, invariant.persistent⟩

theorem Ready.simulation (stored : MENumericalHistory.Stored heap p clock reference addresses buffer)
    (persistent : Persistent program objects retained owners original literals heap p)
    (finished : LifecycleRelease.CanFinish .me reference.control.mode) :
    Ready program objects retained owners original literals heap p reference.control.mode :=
  ⟨stored.control.kind, stored.control.mode, finished, persistent⟩

structure CycleContract (model : Solve.Model source) (program : Program Invocation) (objects : Objects)
    (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (original literals heap : Heap) (p : Address) (access : Float64Buffers.Layout)
    (addresses : String → Address) (buffer : Address) (cycle : Cycle) : Prop where
  initialization : SourceContract model.prepareFMI3 program objects retained owners original literals heap p access
    .me .reset cycle.state cycle.initialization
  simulation : ∀ observed exited checkpoints,
    InitializationProtocol.Completed program p access heap cycle.initialization observed exited checkpoints →
    MEExecution model.prepareFMI3 program objects retained owners original literals exited p addresses buffer
      (InitializationProtocol.meReference cycle.state cycle.args) (Time.Clock.initial cycle.args.start)
      cycle.simulation cycle.final cycle.finalClock
  initializationStopped : ∀ stop, InitializationProtocol.Interrupted program p access heap cycle.initialization stop →
    InitializationProtocol.SourcePrefix model.prepareFMI3 p .me .reset cycle.initialization stop
  simulationStopped : ∀ observed exited checkpoints,
    InitializationProtocol.Completed program p access heap cycle.initialization observed exited checkpoints →
    ∀ stop, MEMixedRun.Interrupted program p addresses buffer exited cycle.simulation stop →
      MEMixedRun.SourcePrefix source p addresses buffer (InitializationProtocol.meReference cycle.state cycle.args)
        (Time.Clock.initial cycle.args.start) cycle.simulation stop

theorem CycleContract.completed
    (certified : CycleContract model program objects retained owners original literals heap p access addresses buffer cycle)
    (initialized : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints)
    (executed : MEMixedRun.Completed program p addresses buffer exited cycle.simulation observed after epochs)
    (guarded : InitializationProtocol.MEOutputsGuarded objects retained addresses buffer) :
    CycleEvidence model p cycle initial checkpoints observed epochs ∧
    MENumericalHistory.Stored after p cycle.finalClock cycle.final addresses buffer ∧ Reset.Storage after p ∧
    Persistent program objects retained owners original literals after p ∧
    CReadOnly.Preserves heap after ∧ InitializationProtocol.Retains p heap after ∧
    (∀ q, MEFailure.Protected objects addresses buffer q → InitializationProtocol.Untouched p access cycle.initialization q →
      MENumericalRun.Outside p addresses buffer q → after q = heap q) := by
  obtain ⟨initialObservations, ivps, _, readonly, keeps, frame⟩ := certified.initialization.completed _ _ _ initialized
  have simulation := certified.simulation _ _ _ initialized
  obtain ⟨stored, reset, persistent, runKeeps, runReadonly, runFrame⟩ := simulation.completed _ _ _ executed
  obtain ⟨config, trace⟩ := simulation.trace
  obtain ⟨observations, epochs⟩ := trace.source model executed
  exact ⟨⟨⟨initialObservations, ivps⟩, observations, epochs⟩, stored, reset, persistent, readonly.trans runReadonly,
    (fun name outside => (runKeeps name outside).trans (keeps name outside)),
    fun q inside untouched outside => (runFrame q inside outside).trans (frame q (guarded.protects inside) untouched)⟩

theorem cycle_contract
    (initialization : InitializationCompiler model program objects retained owners original literals p access)
    (simulation : SimulationCompiler model program objects retained owners original literals p addresses buffer)
    (outputs : MENumericalHistory.CallerStorage original p addresses buffer)
    (guarded : InitializationProtocol.MEOutputsGuarded objects retained addresses buffer)
    (admitted : cycle.Admitted objects retained original p access buffer)
    (invariant : Invariant program objects retained owners original literals heap p .me .reset) :
    CycleContract model program objects retained owners original literals heap p access addresses buffer cycle := by
  have certified := initialization heap cycle.initialization cycle.state invariant admitted.1 admitted.2.1
  refine ⟨certified, ?_, ?_, ?_⟩
  · intro observed exited checkpoints executed
    have ready := (certified.completed _ _ _ executed).2.2.1
    exact simulation exited _ cycle.final _ cycle.finalClock cycle.simulation ready.persistent
      (ready.me_ready admitted.2.2.1 outputs guarded) ready.stored.reset admitted.2.2.2
  · intro stop interrupted
    exact initialization.interrupted invariant admitted.1 admitted.2.1 interrupted
  · intro observed exited checkpoints executed stop interrupted
    have ready := (certified.completed _ _ _ executed).2.2.1
    exact simulation.interrupted ready.persistent
      (ready.me_ready admitted.2.2.1 outputs guarded) ready.stored.reset admitted.2.2.2 interrupted

structure Contract (model : Solve.Model source) (program : Program Invocation) (objects : Objects)
    (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (original literals heap : Heap) (p : Address) (access : Float64Buffers.Layout)
    (addresses : String → Address) (buffer : Address) (plan : Plan) : Prop where
  progress : (∃ records after, Completed program p access addresses buffer heap plan records after) ∨
    Stopped program p access addresses buffer heap plan
  completed : ∀ records after, Completed program p access addresses buffer heap plan records after →
    SourceTrace model p plan records ∧ Ready program objects retained owners original literals after p plan.mode ∧
    CReadOnly.Preserves heap after ∧ InitializationProtocol.Retains p heap after ∧
    (∀ q, MEFailure.Protected objects addresses buffer q → plan.Outside p access addresses buffer q → after q = heap q)
  interrupted : ∀ records stop, Interrupted program p access addresses buffer heap plan records stop →
    SourceInterrupted model p addresses buffer plan records stop

theorem CycleContract.progress
    (certified : CycleContract model program objects retained owners original literals heap p access addresses buffer cycle) :
    (∃ initial exited checkpoints observed after epochs,
      InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints ∧
      MEMixedRun.Completed program p addresses buffer exited cycle.simulation observed after epochs) ∨
    InitializationProtocol.Stopped program p access heap cycle.initialization ∨
    (∃ initial exited checkpoints,
      InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints ∧
      MEMixedRun.Stopped program p addresses buffer exited cycle.simulation) := by
  rcases certified.initialization.progress with ⟨initial, exited, checkpoints, initialized⟩ | stopped
  · rcases (certified.simulation _ _ _ initialized).progress with ⟨observed, after, epochs, completed⟩ | stopped
    · exact Or.inl ⟨initial, exited, checkpoints, observed, after, epochs, initialized, completed⟩
    · exact Or.inr (Or.inr ⟨initial, exited, checkpoints, initialized, stopped⟩)
  · exact Or.inr (Or.inl stopped)

theorem CycleContract.restarted
    (certified : CycleContract model program objects retained owners original literals heap p access addresses buffer cycle)
    (reset : StaticReset.ExecutionContract program)
    (guarded : InitializationProtocol.MEOutputsGuarded objects retained addresses buffer)
    (initialized : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints)
    (executed : MEMixedRun.Completed program p addresses buffer exited cycle.simulation observed after epochs) :
    CycleEvidence model p cycle initial checkpoints observed epochs ∧
    (∀ behavior, (machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] after .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, Reset.finalHeap after p⟩) ∧
    Invariant program objects retained owners original literals (Reset.finalHeap after p) p .me .reset ∧
    CReadOnly.Preserves heap (Reset.finalHeap after p) ∧
    InitializationProtocol.Retains p heap (Reset.finalHeap after p) ∧
    (∀ q, MEFailure.Protected objects addresses buffer q → InitializationProtocol.Untouched p access cycle.initialization q →
      MENumericalRun.Outside p addresses buffer q → Reset.finalHeap after p q = heap q) := by
  obtain ⟨evidence, stored, storage, persistent, readonly, keeps, frame⟩ := certified.completed initialized executed guarded
  obtain ⟨called, invariant, resetReadonly, resetKeeps⟩ := InitializationProtocol.reset_invariant
    (kind := .me) (mode := cycle.final.control.mode) model.prepareFMI3 reset storage stored.control.kind
    stored.mode_loaded persistent.ownership persistent.caller persistent.readonly persistent.logging
  exact ⟨evidence, called, invariant, readonly.trans resetReadonly,
    (fun name outside => (resetKeeps name outside).trans (keeps name outside)),
    fun q inside untouched outside => (StaticReset.record_frame after p q untouched.1).trans
      (frame q inside untouched outside)⟩

/-- Source correspondence for every actual interrupted history, including
prefixes in later cycles. The reset contract excludes a blocked reset outcome. -/
theorem interrupted_correct
    (initialization : InitializationCompiler model program objects retained owners original literals p access)
    (simulation : SimulationCompiler model program objects retained owners original literals p addresses buffer)
    (reset : StaticReset.ExecutionContract program)
    (outputs : MENumericalHistory.CallerStorage original p addresses buffer)
    (guarded : InitializationProtocol.MEOutputsGuarded objects retained addresses buffer)
    (admitted : Admitted objects retained original p access buffer plan)
    (invariant : Invariant program objects retained owners original literals heap p .me .reset)
    (actual : Interrupted program p access addresses buffer heap plan records stop) :
    SourceInterrupted model p addresses buffer plan records stop := by
  induction admitted generalizing heap records stop with
  | finish reference prepared _ =>
    cases actual with
    | finish interrupted => exact .finish (initialization.interrupted invariant reference prepared interrupted)
  | last admitted =>
    have certified := cycle_contract initialization simulation outputs guarded admitted invariant
    cases actual with
    | lastInitialization interrupted => exact .lastInitialization (certified.initializationStopped _ interrupted)
    | lastSimulation initialized interrupted =>
      obtain ⟨observations, checkpoints, _, _, _, _⟩ := certified.initialization.completed _ _ _ initialized
      exact .lastSimulation ⟨observations, checkpoints⟩ (certified.simulationStopped _ _ _ initialized _ interrupted)
  | next admitted _ ih =>
    have certified := cycle_contract initialization simulation outputs guarded admitted invariant
    cases actual with
    | nextInitialization interrupted => exact .nextInitialization (certified.initializationStopped _ interrupted)
    | nextSimulation initialized interrupted =>
      obtain ⟨observations, checkpoints, _, _, _, _⟩ := certified.initialization.completed _ _ _ initialized
      exact .nextSimulation ⟨observations, checkpoints⟩ (certified.simulationStopped _ _ _ initialized _ interrupted)
    | reset initialized simulated blocked =>
      obtain ⟨_, resetCall, _, _, _, _⟩ := certified.restarted reset guarded initialized simulated
      cases (resetCall _).mp blocked
    | later initialized simulated resetActual interrupted =>
      obtain ⟨evidence, resetCall, resetInvariant, _, _, _⟩ := certified.restarted reset guarded initialized simulated
      cases (resetCall _).mp resetActual
      exact .later evidence (ih resetInvariant interrupted)

/-- Induction over whole initialization/simulation cycles. All intermediate
heaps, statuses, resource invariants and source observations are derived from
actual executions, including every returning external-effect branch. -/
theorem correct
    (initialization : InitializationCompiler model program objects retained owners original literals p access)
    (simulation : SimulationCompiler model program objects retained owners original literals p addresses buffer)
    (reset : StaticReset.ExecutionContract program)
    (outputs : MENumericalHistory.CallerStorage original p addresses buffer)
    (guarded : InitializationProtocol.MEOutputsGuarded objects retained addresses buffer)
    (admitted : Admitted objects retained original p access buffer plan)
    (invariant : Invariant program objects retained owners original literals heap p .me .reset) :
    Contract model program objects retained owners original literals heap p access addresses buffer plan := by
  induction admitted generalizing heap with
  | finish reference prepared finished =>
    have certified := initialization heap _ _ invariant reference prepared
    constructor
    · rcases certified.progress with ⟨observed, after, checkpoints, executed⟩ | stopped
      · exact Or.inl ⟨_, after, .finish executed⟩
      · exact Or.inr (.finish stopped)
    · intro records after executed
      cases executed with
      | finish called =>
        obtain ⟨observations, ivps, ready, readonly, keeps, frame⟩ := certified.completed _ _ _ called
        exact ⟨.finish ⟨observations, ivps⟩, Ready.initialization ready finished, readonly, keeps,
          fun q inside outside => frame q (guarded.protects inside) outside⟩
    · intro records stop interrupted
      exact interrupted_correct initialization simulation reset outputs guarded (.finish reference prepared finished) invariant interrupted
  | last admitted =>
    have certified := cycle_contract initialization simulation outputs guarded admitted invariant
    constructor
    · rcases certified.progress with ⟨initial, exited, checkpoints, observed, after, epochs, initialized, simulated⟩ |
        stopped | ⟨initial, exited, checkpoints, initialized, stopped⟩
      · exact Or.inl ⟨_, after, .last initialized simulated⟩
      · exact Or.inr (.lastInitialization stopped)
      · exact Or.inr (.lastSimulation initialized stopped)
    · intro records after executed
      cases executed with
      | last initialized simulated =>
        obtain ⟨evidence, stored, _, persistent, readonly, keeps, frame⟩ := certified.completed initialized simulated guarded
        exact ⟨.last evidence, Ready.simulation stored persistent admitted.can_finish,
          readonly, keeps, fun q inside outside => frame q inside outside.1 outside.2⟩
    · intro records stop interrupted
      exact interrupted_correct initialization simulation reset outputs guarded (.last admitted) invariant interrupted
  | next admitted following ih =>
    have certified := cycle_contract initialization simulation outputs guarded admitted invariant
    constructor
    · rcases certified.progress with ⟨initial, exited, checkpoints, observed, after, epochs, initialized, simulated⟩ |
        stopped | ⟨initial, exited, checkpoints, initialized, stopped⟩
      · obtain ⟨_, resetCall, resetInvariant, _, _, _⟩ := certified.restarted reset guarded initialized simulated
        have next := ih resetInvariant
        rcases next.progress with ⟨records, final, completed⟩ | stopped
        · exact Or.inl ⟨_, final, .next initialized simulated ((resetCall _).mpr rfl) completed⟩
        · exact Or.inr (.later initialized simulated ((resetCall _).mpr rfl) stopped)
      · exact Or.inr (.nextInitialization stopped)
      · exact Or.inr (.nextSimulation initialized stopped)
    · intro records after executed
      cases executed with
      | next initialized simulated resetActual following =>
        obtain ⟨evidence, resetCall, resetInvariant, readonly, keeps, frame⟩ := certified.restarted reset guarded initialized simulated
        cases (resetCall _).mp resetActual
        obtain ⟨sourceTrace, ready, laterReadonly, laterKeeps, laterFrame⟩ := (ih resetInvariant).completed _ _ following
        exact ⟨.next evidence sourceTrace, ready, readonly.trans laterReadonly,
          (fun name outside => (laterKeeps name outside).trans (keeps name outside)),
          fun q inside outside => (laterFrame q inside outside.2.2).trans (frame q inside outside.1 outside.2.1)⟩
    · intro records stop interrupted
      exact interrupted_correct initialization simulation reset outputs guarded (.next admitted following) invariant interrupted

theorem Contract.stopped_source
    (certified : Contract model program objects retained owners original literals heap p access addresses buffer plan)
    (actual : Stopped program p access addresses buffer heap plan) :
    ∃ records stop, Interrupted program p access addresses buffer heap plan records stop ∧
      SourceInterrupted model p addresses buffer plan records stop := by
  obtain ⟨records, stop, interrupted⟩ := actual.interrupted
  exact ⟨records, stop, interrupted, certified.interrupted _ _ interrupted⟩

/-- Progress carries source evidence for either outcome; blocking never
turns a pending call into a successful numerical or initialization observation. -/
theorem Contract.progress_source
    (certified : Contract model program objects retained owners original literals heap p access addresses buffer plan) :
    (∃ records after, Completed program p access addresses buffer heap plan records after ∧ SourceTrace model p plan records) ∨
    (∃ records stop, Interrupted program p access addresses buffer heap plan records stop ∧
      SourceInterrupted model p addresses buffer plan records stop) := by
  rcases certified.progress with ⟨records, after, completed⟩ | stopped
  · exact Or.inl ⟨records, after, completed, (certified.completed _ _ completed).1⟩
  · exact Or.inr (certified.stopped_source stopped)

/-- Every completed recurring history can terminate and release the original
slot. The suffix has complete actual call contracts, not assumed successes. -/
theorem Contract.released {program : Program Invocation}
    (objects : Objects) (tag : CAtomicBoolean.Calls.Event → Invocation) (slot : Fin objects.capacity)
    {owners : SlotOwners.State objects.capacity}
    (certified : Contract model program objects retained owners original literals heap
      (objects.instances.index slot.val) access addresses buffer plan)
    (termination : Termination.ReleaseContract objects program tag) (release : StaticRelease.Bindings program tag)
    (flags : interface.constants "rumoca_instance_flags" = some (.pointer (some ⟨objects.flagsBlock, [], 0⟩)))
    (owned : owners slot = some owner)
    (metadata : load heap ((objects.instances.index slot.val).member "slot") = some (.integer slot.val))
    (executed : Completed program (objects.instances.index slot.val) access addresses buffer heap plan records after) :
    SourceTrace model (objects.instances.index slot.val) plan records ∧
    LifecycleRelease.Released objects program tag after slot owners owner .me plan.mode ∧
    (∀ q, MEFailure.Protected objects addresses buffer q → plan.Outside (objects.instances.index slot.val) access addresses buffer q →
      q ≠ AtomicSlots.address objects.flagsBlock slot →
      LifecycleRelease.releasedHeap after objects slot plan.mode q = heap q) := by
  obtain ⟨sourceTrace, ready, _, keeps, frame⟩ := certified.completed _ _ executed
  have metadataAfter : load after ((objects.instances.index slot.val).member "slot") = some (.integer slot.val) := by
    simpa only [load, keeps "slot" (by decide)] using metadata
  have released := LifecycleRelease.finish_correct objects program tag termination release flags after slot .me plan.mode
    owners owner ready.kindValue ready.modeValue ready.finishable ready.persistent.ownership owned metadataAfter
  refine ⟨sourceTrace, released, ?_⟩
  intro q inside outside notFlag
  have notMode : q ≠ (objects.instances.index slot.val).member "mode" :=
    fun same => outside.not_record (same ▸ (objects.instances.index slot.val).member_in_record "mode")
  exact (released.frame q notMode notFlag).trans (frame q inside outside)

end Rumoca.FMI3.MEProtocol
end
