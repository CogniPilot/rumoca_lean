import RumocaFMI3.CSRunExecution
import Rumoca.FMI3Restart

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CBody StaticFactory

/-- A run's source IVP uses its own time origin and selected initial value.
This does not claim that the current numerical sample is the initial sample. -/
def CSRun.SourceEpoch (source : AST.Model) (reference : CSRun.Reference) (trajectory : ℝ → ℝ) : Prop :=
  Source.Initializes source (Binary64.value reference.start) trajectory ∧
  trajectory (Binary64.value reference.start) = Binary64.value reference.seed

theorem CSRun.SourceEpoch.unique (epoch : CSRun.SourceEpoch source reference trajectory) :
    trajectory = Initialization.trajectory (Binary64.value reference.start) (Binary64.value reference.seed) :=
  Initialization.completed_solution_unique _ ⟨Binary64.value reference.seed, []⟩ _ _ epoch.1.2 epoch.2

theorem CSRun.source_epoch (model : Solve.Model source) (reference : CSRun.Reference) :
    ∃! trajectory, CSRun.SourceEpoch source reference trajectory := by
  refine ⟨Initialization.trajectory (Binary64.value reference.start) (Binary64.value reference.seed),
    ⟨⟨model.dae.flat.resolved, Initialization.unfixed_start_is_free none _ _⟩,
      Initialization.trajectory_initial _ _⟩, ?_⟩
  intro trajectory epoch
  exact epoch.unique

/-- Every stored state in the mixed trace has an actual readable binary64
sample with the existing numerical/clock error bound for that source epoch. -/
theorem CSRun.Stored.source_observation {model : Solve.Model source} {buffers : StepEntry.Buffers}
    (stored : CSRun.Stored model heap p buffers reference)
    (epoch : CSRun.SourceEpoch source reference trajectory) :
    ∃ value : Binary64.Value, load heap (StateProofs.stateAddress p) = some (.finite value) ∧
      |Binary64.value value - trajectory (Binary64.value reference.current.time)| ≤
        (reference.current.elapsed : ℝ) +
          |Binary64.value reference.current.time - (Binary64.value reference.start + (reference.current.elapsed : ℝ))| := by
  refine ⟨model.run reference.seed reference.current.elapsed, ?_, ?_⟩
  · simp [load, stored.state, Value.finite, convert]
  · rw [epoch.unique]
    exact model.run_error_at_time reference.seed reference.current.elapsed
      (Binary64.value reference.start) (Binary64.value reference.current.time)

/-- The actual adapter certificate supplies every function and prepared
contract used by the mixed CS trace. Only original storage, host configuration
and foreign-library conditions are premises; all later call heaps are derived. -/
theorem adapter_cs_run_history (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (header : CFenv.Header) (objects : Objects) (firstBlock : Nat)
        (literalBase : Heap) (signed : Bool),
      letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
      ∀ (program : CCalls.Events.Program E)
        (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
      program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
      program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
      program.externals "floor" = some (CMathCalls.floorExternal rfl) →
      ∀ (heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
        (before final : CSRun.Reference) (actions : List CSRun.Action) (statuses : List Int),
      CReadOnly.Preserves (pool.install literalBase firstBlock signed) heap →
      CSRun.Stored a.solve heap p buffers before → CSRun.Suppressed heap p →
      CSRun.ReferenceTrace header p buffers before actions final statuses →
      ∃ after, CSRun.Calls a.solve program p buffers heap before actions after final statuses ∧
        CSRun.Stored a.solve after p buffers final ∧ CSRun.Retains p heap after ∧
        CReadOnly.Preserves heap after ∧ CAtomicBoolean.Preserves heap after ∧
        (∃! trajectory, CSRun.SourceEpoch a.parsed.ast final trajectory) ∧
        (∀ trajectory, CSRun.SourceEpoch a.parsed.ast final trajectory →
          ∃ value : Binary64.Value, load after (StateProofs.stateAddress p) = some (.finite value) ∧
            |Binary64.value value - trajectory (Binary64.value final.current.time)| ≤
              (final.current.elapsed : ℝ) +
                |Binary64.value final.current.time - (Binary64.value final.start + (final.current.elapsed : ℝ))|) := by
  obtain ⟨signatures, unique, resetMember, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, initialization, _, _, _, _, _, _, _, _, step⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E header objects firstBlock literalBase signed
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program range actual rounding floorBound heap p buffers before final actions statuses literalFrame stored quiet trace
  have reset : StaticReset.ExecutionContract program := by
    apply ResetEnvironment.execution_correct header objects (pool.addresses firstBlock) a.solve.prepareFMI3 program
    rw [actual]
    exact LiteralPreparation.function_bound _ signatures unique _ resetMember
  have enterDefined : program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) := by
    rw [actual, ← InitializationCalls.function_eq a.solve.prepareFMI3]
    exact LiteralPreparation.function_bound _ signatures unique _ initialization.enterMember
  have exitDefined : program.internal.definitions InitializationExit.signature.name =
      some (.tree (Runtime.function a.solve.prepareFMI3 InitializationExit.signature)) := by
    rw [actual]
    exact LiteralPreparation.function_bound _ signatures unique _ initialization.exitMember
  obtain ⟨after, calls, finalStored, retained, readonly, atomic⟩ := CSRun.trace_correct header objects a.solve.prepareFMI3 signatures pool
    (step.prepared pool made) literalBase firstBlock signed p buffers program range actual rounding floorBound reset
    enterDefined exitDefined heap before final actions statuses literalFrame stored quiet trace
  exact ⟨after, calls, finalStored, retained, readonly, atomic, CSRun.source_epoch a.solve final,
    fun _ epoch => finalStored.source_observation epoch⟩

end Rumoca.FMI3
end
