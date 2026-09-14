import RumocaFMI3.CSInitializationProtocol
import Rumoca.FMI3InitializationProtocol
import Rumoca.FMI3CSRunRecords

noncomputable section
namespace Rumoca.FMI3.CSProtocol
open CMemory StaticFactory CCalls.Events
open InitializationProtocol (Invariant Persistent CSExecution SourceContract)

variable {source : AST.Model} {model : Solve.FMI3Model source}

structure InitializationEvidence (model : Solve.FMI3Model source) (p : Address)
    (actions : List InitializationProtocol.Action) (observed : List (Float64Access.Observation Invocation))
    (checkpoints : List Heap) : Prop where
  observations : InitializationProtocol.Observed model .reset actions observed
  sourceIVPs : List.Forall₂ (InitializationProtocol.SourceCheckpoint source p)
    (InitializationProtocol.exitStates .reset actions) checkpoints

structure CycleEvidence (model : Solve.FMI3Model source) (header : CFenv.Header) (p : Address)
    (buffers : StepEntry.Buffers) (cycle : Cycle)
    (initial : List (Float64Access.Observation Invocation)) (checkpoints : List Heap)
    (exited : Heap) (statuses : List Int) (calls : List (CSRun.CallRecord Invocation)) (after : Heap) : Prop where
  initialization : InitializationEvidence model p cycle.initialization initial checkpoints
  statuses_eq : statuses = cycle.statuses
  callSources : CSRun.SourceTrace source header p buffers exited
    (InitializationProtocol.csReference cycle.state cycle.args) cycle.simulation statuses calls after cycle.final
  sourceEpoch : ∃! trajectory, CSRun.SourceEpoch source cycle.final trajectory
  sample : ∀ trajectory, CSRun.SourceEpoch source cycle.final trajectory →
    ∃ value : Binary64.Value, load after (StateProofs.stateAddress p) = some (.finite value) ∧
      |Binary64.value value - trajectory (Binary64.value cycle.final.current.time)| ≤
        (cycle.final.current.elapsed : ℝ) +
          |Binary64.value cycle.final.current.time -
            (Binary64.value cycle.final.start + (cycle.final.current.elapsed : ℝ))|

/-- Retain initialization checkpoints, every simulation call and segment-final
source samples across resets. Reset results are postconditions. -/
inductive SourceTrace (model : Solve.FMI3Model source) (header : CFenv.Header) (p : Address)
    (buffers : StepEntry.Buffers) : Plan → List Record → Prop where
  | finish : InitializationEvidence model p actions observed checkpoints →
      SourceTrace model header p buffers (.finish actions state) [.initialization observed checkpoints after]
  | last : CycleEvidence model header p buffers cycle initial checkpoints exited statuses calls after →
      SourceTrace model header p buffers (.last cycle)
        [.initialization initial checkpoints exited, .simulation statuses events calls after]
  | next : CycleEvidence model header p buffers cycle initial checkpoints exited statuses calls simulated →
      SourceTrace model header p buffers following records →
      SourceTrace model header p buffers (.next cycle following)
        (.initialization initial checkpoints exited :: .simulation statuses events calls simulated ::
          .reset [] (.integer 0) (Reset.finalHeap simulated p) :: records)

structure Ready [CInterface] (program : Program Invocation) (objects : Objects) (retained : Address → Prop)
    (owners : SlotOwners.State objects.capacity) (original literals heap : Heap) (p : Address) (mode : Mode) : Prop where
  kindValue : load heap (p.member "kind") = some (.integer Kind.cs.code)
  modeValue : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩
  finishable : LifecycleRelease.CanFinish .cs mode
  persistent : Persistent program objects retained owners original literals heap p

variable [interface : CInterface] {program : Program Invocation} {objects : Objects} {owners : SlotOwners.State objects.capacity}

theorem Ready.initialization
    (invariant : Invariant program objects retained owners original literals heap p .cs state)
    (finished : state.phase.Finished) : Ready program objects retained owners original literals heap p (state.phase.mode .cs) :=
  ⟨invariant.stored.instanceStored.kind, invariant.stored.instanceStored.mode,
    state.phase.can_finish .cs finished, invariant.persistent⟩

theorem Ready.simulation (stored : CSRun.Stored model.solve heap p buffers reference)
    (persistent : Persistent program objects retained owners original literals heap p)
    (finished : CSRun.CanFinish reference.mode) : Ready program objects retained owners original literals heap p reference.mode := by
  refine ⟨stored.kind, stored.mode_cell, ?_, persistent⟩
  rcases finished with active | stopped
  · exact Or.inl (by simp [active, Reference.Allowed])
  · exact Or.inr stopped

structure CycleContract (model : Solve.FMI3Model source) (header : CFenv.Header) (program : Program Invocation) (objects : Objects)
    (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (original literals heap : Heap) (p : Address) (access : Float64Buffers.Layout) (buffers : StepEntry.Buffers) (cycle : Cycle) : Prop where
  initialization : SourceContract model program objects retained owners original literals heap p access
    .cs .reset cycle.state cycle.initialization
  simulation : ∀ observed exited checkpoints,
    InitializationProtocol.Completed program p access heap cycle.initialization observed exited checkpoints →
    CSExecution model header program objects retained owners original literals exited p buffers
      (InitializationProtocol.csReference cycle.state cycle.args) cycle.simulation cycle.final cycle.statuses

theorem CycleContract.completed
    (certified : CycleContract model header program objects retained owners original literals heap p access buffers cycle)
    (initialized : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints)
    (executed : CSRun.Recorded program p exited cycle.simulation statuses events after calls)
    (guarded : InitializationProtocol.CSOutputsGuarded objects retained buffers) :
    CycleEvidence model header p buffers cycle initial checkpoints exited statuses calls after ∧
    CSRun.Stored model.solve after p buffers cycle.final ∧
    Persistent program objects retained owners original literals after p ∧
    CReadOnly.Preserves heap after ∧ InitializationProtocol.Retains p heap after ∧
    (∀ q, CSRun.Protected objects buffers q → InitializationProtocol.Untouched p access cycle.initialization q →
      CSRun.Outside p buffers q → after q = heap q) := by
  obtain ⟨observations, ivps, _, readonly, keeps, frame⟩ := certified.initialization.completed _ _ _ initialized
  obtain ⟨same, stored, persistent, runKeeps, runReadonly, runFrame⟩ :=
    (certified.simulation _ _ _ initialized).completed _ _ _ executed.completed
  exact ⟨⟨⟨observations, ivps⟩, same, ((certified.simulation _ _ _ initialized).semantic _ _ _ _ executed).source_observations,
      CSRun.source_epoch model.solve cycle.final,
      fun _ epoch => stored.source_observation epoch⟩, stored, persistent, readonly.trans runReadonly,
    (fun name outside => (runKeeps name outside).trans (keeps name outside)),
    fun q inside untouched outside => (runFrame q inside outside).trans (frame q (guarded.protects inside) untouched)⟩

def InitializationCompiler (model : Solve.FMI3Model source) (program : Program Invocation) (objects : Objects)
    (retained : Address → Prop) (owners : SlotOwners.State objects.capacity) (original literals : Heap)
    (p : Address) (access : Float64Buffers.Layout) : Prop :=
  ∀ heap actions state, Invariant program objects retained owners original literals heap p .cs .reset →
    InitializationProtocol.ReferenceTrace .cs .reset actions state →
    (∀ action ∈ actions, action.Prepared objects retained original p access) →
    SourceContract model program objects retained owners original literals heap p access .cs .reset state actions

def SimulationCompiler (model : Solve.FMI3Model source) (program : Program Invocation) (header : CFenv.Header)
    (objects : Objects) (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (original literals : Heap) (p : Address) (buffers : StepEntry.Buffers) : Prop :=
  ∀ heap before final actions statuses,
    Persistent program objects retained owners original literals heap p →
    CSRun.Stored model.solve heap p buffers before → CSRun.ReferenceTrace header p buffers before actions final statuses →
    CSExecution model header program objects retained owners original literals heap p buffers before actions final statuses

theorem cycle_contract
    (initialization : InitializationCompiler model program objects retained owners original literals p access)
    (simulation : SimulationCompiler model program header objects retained owners original literals p buffers)
    (outputs : StepArguments.Storage original p buffers)
    (guarded : InitializationProtocol.CSOutputsGuarded objects retained buffers)
    (admitted : cycle.Admitted header objects retained original p access buffers)
    (invariant : Invariant program objects retained owners original literals heap p .cs .reset) :
    CycleContract model header program objects retained owners original literals heap p access buffers cycle := by
  have certified := initialization heap cycle.initialization cycle.state invariant admitted.1 admitted.2.1
  refine ⟨certified, ?_⟩
  intro observed exited checkpoints executed
  have ready := (certified.completed _ _ _ executed).2.2.1
  exact simulation exited _ cycle.final cycle.simulation cycle.statuses ready.persistent
    (ready.cs_ready model.solve admitted.2.2.1 outputs guarded) admitted.2.2.2

structure Contract (model : Solve.FMI3Model source) (header : CFenv.Header) (program : Program Invocation) (objects : Objects)
    (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (original literals heap : Heap) (p : Address) (access : Float64Buffers.Layout) (buffers : StepEntry.Buffers) (plan : Plan) : Prop where
  progress : (∃ records after, Completed program p access heap plan records after) ∨ Stopped program p access heap plan
  completed : ∀ records after, Completed program p access heap plan records after →
    SourceTrace model header p buffers plan records ∧ Ready program objects retained owners original literals after p plan.mode ∧
    CReadOnly.Preserves heap after ∧ InitializationProtocol.Retains p heap after ∧
    (∀ q, CSRun.Protected objects buffers q → plan.Outside p access buffers q → after q = heap q)

theorem CycleContract.progress
    (certified : CycleContract model header program objects retained owners original literals heap p access buffers cycle) :
    (∃ initial exited checkpoints statuses events after calls,
      InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints ∧
      CSRun.Recorded program p exited cycle.simulation statuses events after calls) ∨
    InitializationProtocol.Stopped program p access heap cycle.initialization ∨
    (∃ initial exited checkpoints,
      InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints ∧
      CSRun.Stopped program p exited cycle.simulation) := by
  rcases certified.initialization.progress with ⟨initial, exited, checkpoints, initialized⟩ | stopped
  · rcases (certified.simulation _ _ _ initialized).progress with ⟨events, after, completed⟩ | stopped
    · obtain ⟨calls, recorded⟩ := completed.records
      exact Or.inl ⟨initial, exited, checkpoints, cycle.statuses, events, after, calls, initialized, recorded⟩
    · exact Or.inr (Or.inr ⟨initial, exited, checkpoints, initialized, stopped⟩)
  · exact Or.inr (Or.inl stopped)

theorem CycleContract.restarted
    (certified : CycleContract model header program objects retained owners original literals heap p access buffers cycle)
    (reset : StaticReset.ExecutionContract program)
    (guarded : InitializationProtocol.CSOutputsGuarded objects retained buffers)
    (initialized : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints)
    (executed : CSRun.Recorded program p exited cycle.simulation statuses events after calls) :
    CycleEvidence model header p buffers cycle initial checkpoints exited statuses calls after ∧
    (∀ behavior, (machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] after .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, Reset.finalHeap after p⟩) ∧
    Invariant program objects retained owners original literals (Reset.finalHeap after p) p .cs .reset ∧
    CReadOnly.Preserves heap (Reset.finalHeap after p) ∧
    InitializationProtocol.Retains p heap (Reset.finalHeap after p) ∧
    (∀ q, CSRun.Protected objects buffers q → InitializationProtocol.Untouched p access cycle.initialization q →
      CSRun.Outside p buffers q → Reset.finalHeap after p q = heap q) := by
  obtain ⟨evidence, stored, persistent, readonly, keeps, frame⟩ := certified.completed initialized executed guarded
  obtain ⟨called, invariant, resetReadonly, resetKeeps⟩ := InitializationProtocol.reset_invariant
    (kind := .cs) (mode := cycle.final.mode) model reset
    stored.reset stored.kind stored.mode persistent.ownership persistent.caller persistent.readonly persistent.logging
  exact ⟨evidence, called, invariant, readonly.trans resetReadonly,
    (fun name outside => (resetKeeps name outside).trans (keeps name outside)),
    fun q inside untouched outside => (StaticReset.record_frame after p q untouched.1).trans
      (frame q inside untouched outside)⟩

/-- Induction over whole initialization/simulation cycles. All intermediate
heaps, statuses, resource invariants and source observations are derived from
actual executions, including every returning external-effect branch. -/
theorem correct
    (initialization : InitializationCompiler model program objects retained owners original literals p access)
    (simulation : SimulationCompiler model program header objects retained owners original literals p buffers)
    (reset : StaticReset.ExecutionContract program)
    (outputs : StepArguments.Storage original p buffers)
    (guarded : InitializationProtocol.CSOutputsGuarded objects retained buffers)
    (admitted : Admitted header objects retained original p access buffers plan)
    (invariant : Invariant program objects retained owners original literals heap p .cs .reset) :
    Contract model header program objects retained owners original literals heap p access buffers plan := by
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
  | last admitted =>
    have certified := cycle_contract initialization simulation outputs guarded admitted invariant
    constructor
    · rcases certified.progress with ⟨initial, exited, checkpoints, statuses, events, after, calls, initialized, simulated⟩ |
        stopped | ⟨initial, exited, checkpoints, initialized, stopped⟩
      · exact Or.inl ⟨_, after, .last initialized simulated⟩
      · exact Or.inr (.lastInitialization stopped)
      · exact Or.inr (.lastSimulation initialized stopped)
    · intro records after executed
      cases executed with
      | last initialized simulated =>
        obtain ⟨evidence, stored, persistent, readonly, keeps, frame⟩ := certified.completed initialized simulated guarded
        exact ⟨.last evidence, Ready.simulation stored persistent (admitted.2.2.2.can_finish (Or.inl rfl)),
          readonly, keeps, fun q inside outside => frame q inside outside.1 outside.2⟩
  | next admitted _ ih =>
    have certified := cycle_contract initialization simulation outputs guarded admitted invariant
    constructor
    · rcases certified.progress with ⟨initial, exited, checkpoints, statuses, events, after, calls, initialized, simulated⟩ |
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

/-- Every completed recurring history can terminate and release the original
slot. The suffix has complete actual call contracts, not assumed successes. -/
theorem Contract.released {program : Program Invocation}
    (objects : Objects) (tag : CAtomicBoolean.Calls.Event → Invocation) (slot : Fin objects.capacity)
    {owners : SlotOwners.State objects.capacity}
    (certified : Contract model header program objects retained owners original literals heap
      (objects.instances.index slot.val) access buffers plan)
    (termination : Termination.ReleaseContract objects program tag) (release : StaticRelease.Bindings program tag)
    (flags : interface.constants "rumoca_instance_flags" = some (.pointer (some ⟨objects.flagsBlock, [], 0⟩)))
    (owned : owners slot = some owner)
    (metadata : load heap ((objects.instances.index slot.val).member "slot") = some (.integer slot.val))
    (executed : Completed program (objects.instances.index slot.val) access heap plan records after) :
    SourceTrace model header (objects.instances.index slot.val) buffers plan records ∧
    LifecycleRelease.Released objects program tag after slot owners owner .cs plan.mode ∧
    (∀ q, CSRun.Protected objects buffers q → plan.Outside (objects.instances.index slot.val) access buffers q →
      q ≠ AtomicSlots.address objects.flagsBlock slot →
      LifecycleRelease.releasedHeap after objects slot plan.mode q = heap q) := by
  obtain ⟨sourceTrace, ready, _, keeps, frame⟩ := certified.completed _ _ executed
  have metadataAfter : load after ((objects.instances.index slot.val).member "slot") = some (.integer slot.val) := by
    simpa only [load, keeps "slot" (by decide)] using metadata
  have released := LifecycleRelease.finish_correct objects program tag termination release flags after slot .cs plan.mode
    owners owner ready.kindValue ready.modeValue ready.finishable ready.persistent.ownership owned metadataAfter
  refine ⟨sourceTrace, released, ?_⟩
  intro q inside outside notFlag
  have notMode : q ≠ (objects.instances.index slot.val).member "mode" :=
    fun same => outside.not_record (same ▸ (objects.instances.index slot.val).member_in_record "mode")
  exact (released.frame q notMode notFlag).trans (frame q inside outside)

end Rumoca.FMI3.CSProtocol
end
