import RumocaFMI3.InitializationProtocolEnvironment
import Rumoca.FMI3InitializationAccess
import RumocaFMI3.CountMetadata
import RumocaFMI3.NominalMetadata

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CMemory StaticFactory CLiteral CCalls.Events

variable {source : AST.Model} {model : Solve.FMI3Model source}

def trajectory (state : State) : ℝ → ℝ :=
  Initialization.trajectory (Binary64.value state.time) (Binary64.value state.value.x)

def SourceCheckpoint (source : AST.Model) (p : Address) (state : State) (heap : Heap) : Prop :=
  InitializationCalls.SourceInitialized source heap p state.time (trajectory state) ∧
  ∀ candidate, InitializationCalls.SourceInitialized source heap p state.time candidate → candidate = trajectory state

theorem Stored.source_ivp (model : Solve.FMI3Model source) (stored : Stored heap p kind state) :
    SourceCheckpoint source p state heap :=
  ⟨InitializationCalls.model_source_initialized source heap p state.time state.value
      model.solve.dae.flat.resolved stored.instanceStored.represented,
    fun _ initialized => InitializationCalls.source_initialized_unique initialized stored.instanceStored.represented⟩

theorem Checkpoints.source_ivps (model : Solve.FMI3Model source)
    (checked : Checkpoints p kind state actions heaps) :
    List.Forall₂ (SourceCheckpoint source p) (exitStates state actions) heaps := by
  have stored := checked.stored
  clear checked
  generalize states : exitStates state actions = references at stored ⊢
  clear states
  induction stored with
  | nil => exact .nil
  | cons head _ ih => exact .cons (head.source_ivp model) ih

variable {objects : Objects} {owners : SlotOwners.State objects.capacity}
variable {readers : ReadBank}

/-- This contract covers arbitrary finite initialization protocols, including
repeated failed attempts and resets. Every exit is paired with its actual heap
and unique source IVP. The external logger may block; no completed script is
assumed in the progress branch. -/
structure SourceContract [CInterface] (model : Solve.FMI3Model source) (program : Program Invocation)
    (objects : Objects) (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (original literals heap : Heap) (p : Address) (buffers : Float64Buffers.Layout)
    (kind : Kind) (state final : State) (actions : List Action) (readers : ReadBank) : Prop where
  progress : (∃ observed after checkpoints, Completed program p buffers heap actions observed after checkpoints) ∨
    Stopped program p buffers heap actions
  completed : ∀ observed after checkpoints, Completed program p buffers heap actions observed after checkpoints →
    Observed model state actions observed ∧
    List.Forall₂ (SourceCheckpoint source p) (exitStates state actions) checkpoints ∧
    Invariant program objects retained owners original literals after p kind final readers ∧
    CReadOnly.Preserves heap after ∧ Retention (loggingUpdate actions) p heap after ∧
    (∀ q, Float64Rejection.Protected objects retained q → Untouched p buffers actions q → after q = heap q)

theorem source_contract [CInterface] {program : Program Invocation}
    (contract : ExecutionContract model program objects retained owners original literals p buffers kind readers)
    (reference : ReferenceTrace kind state actions final)
    (prepared : ∀ action ∈ actions, action.Prepared objects retained original p buffers readers)
    (invariant : Invariant program objects retained owners original literals heap p kind state readers) :
    SourceContract model program objects retained owners original literals heap p buffers kind state final actions readers := by
  refine ⟨progress contract reference prepared invariant, ?_⟩
  intro observed after checkpoints executed
  obtain ⟨observations, exits, finalInvariant, readonly, retains, frame⟩ :=
    executed.correct contract reference prepared invariant
  exact ⟨observations, exits.source_ivps model, finalInvariant, readonly, retains, frame⟩

/-- The source, generated numerical C, XML metadata and printed adapter share
one prepared table/pool. Original valid storage and the host's pure request
sequence suffice; future call results and heaps are derived by induction. -/
theorem runtime_source (compiled : compile input = .ok a)
    (build : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    Float64Metadata.Contract a.solve.prepareFMI3 metadata ∧
    Float64SetMetadata.Contract a.parsed.ast metadata ∧
    CountMetadata.Contract a.solve.prepareFMI3 metadata ∧
    NominalMetadata.Contract a.parsed.ast metadata ∧
    DebugLogging.MetadataContract metadata "logStatus" ∧
    (∀ state d, Source.Equation a.parsed.ast d ↔
      d a.parsed.ast.state = Binary64.value (ModelExchange.derivative a.solve state)) ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      LifecycleEnvironment.PreparedContract a.solve.prepareFMI3 sigs ∧
      ∀ (header : CFenv.Header) (objects : Objects) (baseHeap : Heap) (firstBlock : Nat) (signed : Bool),
        letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
        ∀ (program : Program Invocation), program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs →
        program.externals "strcmp" = some (CStringCalls.compareExternal (by rfl)) →
        ∀ (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
          (original heap : Heap) (p : Address) (buffers : Float64Buffers.Layout) (kind : Kind)
          (state final : State) (actions : List Action) (readers : ReadBank),
          Resources objects retained original p buffers readers →
          Invariant program objects retained owners original (pool.install baseHeap firstBlock signed) heap p kind state readers →
          ReferenceTrace kind state actions final →
          (∀ action ∈ actions, action.Prepared objects retained original p buffers readers) →
          SourceContract a.solve.prepareFMI3 program objects retained owners original
            (pool.install baseHeap firstBlock signed) heap p buffers kind state final actions readers := by
  obtain ⟨sigs, unique, resetMember, printed, _, functions, _, _, queries, ready, _, _, _, nominals, _, _, getter, setter,
    initialization, _, _, runtime, termination, _, _, _, _, _, logging, eventContract⟩ := build.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  have getPrepared := Float64Environment.prepared_correct a.solve.prepareFMI3 sigs unique getter.member getter.numerical.fresh made
  have setPrepared := Float64SetEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique setter.member made
  have countPrepared : ∀ events, CountEnvironment.PreparedContract a.solve.prepareFMI3 sigs events pool := by
    letI : StaticLiterals := ⟨fun _ => none⟩
    exact fun events => (queries inferInstance events).prepared pool made
  have nominalPrepared := nominals.runtime pool made
  have loggingPrepared := logging.prepared pool made
  have eventPrepared := eventContract.runtime pool made
  have lifecycle : LifecycleEnvironment.PreparedContract a.solve.prepareFMI3 sigs :=
    ⟨LiteralPreparation.function_bound _ sigs unique _ resetMember,
      by rw [← InitializationCalls.function_eq a.solve.prepareFMI3]; exact LiteralPreparation.function_bound _ sigs unique _ initialization.enterMember,
      LiteralPreparation.function_bound _ sigs unique _ initialization.exitMember,
      LiteralPreparation.function_bound _ sigs unique _ termination.member, runtime.release_defined⟩
  refine ⟨compiled, build.numerical, Float64Metadata.artifact_variables _ _ build.metadata,
    Float64SetMetadata.artifact_state _ _ build.metadata, CountMetadata.artifact_counts _ _ build.metadata,
    NominalMetadata.artifact_nominals _ _ build.metadata,
    DebugLogging.artifact_category _ _ build.metadata,
    derivative_value_source a.solve,
    sigs, pool, made, printed, functions, lifecycle, ?_⟩
  intro header objects baseHeap firstBlock signed
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual compare retained owners original heap p buffers kind state final actions readers resources invariant reference prepared
  exact source_contract (execution_contract header objects a.solve.prepareFMI3 sigs pool getPrepared setPrepared countPrepared nominalPrepared loggingPrepared eventPrepared lifecycle
    baseHeap firstBlock signed program actual compare retained owners original p buffers kind readers resources) reference prepared invariant

end Rumoca.FMI3.InitializationProtocol
end
