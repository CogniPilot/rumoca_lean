import Rumoca.FMI3CSRun
import RumocaFMI3.CSRunLoggedExecution
import RumocaFMI3.CSRunProgress

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CBody StaticFactory

/-- The source consequence applies to every completed actual C script in a
branching history. It does not presume that a foreign logger returns. -/
theorem CSRun.LoggedTrace.source_observation [CInterface] {program : CCalls.Events.Program CCalls.Events.Invocation}
    {logger : CSRun.Logger} {owners : SlotOwners.State objects.capacity} {model : Solve.Model source}
    (certified : CSRun.LoggedTrace objects logger owners model program p buffers heap before actions final statuses)
    (completed : CSRun.Completed program p heap actions observed events after) :
    (∃! trajectory, CSRun.SourceEpoch source final trajectory) ∧
    (∀ trajectory, CSRun.SourceEpoch source final trajectory →
      ∃ value : Binary64.Value, load after (StateProofs.stateAddress p) = some (.finite value) ∧
        |Binary64.value value - trajectory (Binary64.value final.current.time)| ≤
          (final.current.elapsed : ℝ) +
            |Binary64.value final.current.time - (Binary64.value final.start + (final.current.elapsed : ℝ))|) := by
  have same := certified.statuses_eq completed
  subst observed
  have stored := (certified.completed completed).1
  exact ⟨CSRun.source_epoch model final, fun _ epoch => stored.source_observation epoch⟩

/-- Required actual-adapter contracts supply the mixed callback-enabled
history. Original storage and a universal external callback frame suffice;
all subsequent returned heaps, successful outputs and leases are derived. -/
theorem adapter_logged_cs_run_history (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (header : CFenv.Header) (objects : Objects) (firstBlock : Nat)
        (literalBase : Heap) (signed : Bool),
      letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
      ∀ (program : CCalls.Events.Program CCalls.Events.Invocation)
        (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31) (logger : CSRun.Logger),
      program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
      program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
      program.externals "floor" = some (CMathCalls.floorExternal rfl) → logger.Bound program →
      ∀ (heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
        (before final : CSRun.Reference) (actions : List CSRun.Action) (statuses : List Int)
        (owners : SlotOwners.State objects.capacity),
      p.block = objects.instances.block → logger.Respects objects buffers →
      CReadOnly.Preserves (pool.install literalBase firstBlock signed) heap →
      CSRun.Stored a.solve heap p buffers before → logger.Stored heap p →
      SlotOwners.Represents objects.flagsBlock heap owners →
      CSRun.ReferenceTrace header p buffers before actions final statuses →
      CSRun.LoggedTrace objects logger owners a.solve program p buffers heap before actions final statuses ∧
      ((∃ events after, CSRun.Completed program p heap actions statuses events after) ∨
        CSRun.Stopped program p heap actions) ∧
      (∀ observed events after, CSRun.Completed program p heap actions observed events after →
        observed = statuses ∧
        CSRun.Stored a.solve after p buffers final ∧
        SlotOwners.Represents objects.flagsBlock after owners ∧
        (∃! trajectory, CSRun.SourceEpoch a.parsed.ast final trajectory) ∧
        (∀ trajectory, CSRun.SourceEpoch a.parsed.ast final trajectory →
          ∃ value : Binary64.Value, load after (StateProofs.stateAddress p) = some (.finite value) ∧
            |Binary64.value value - trajectory (Binary64.value final.current.time)| ≤
              (final.current.elapsed : ℝ) +
                |Binary64.value final.current.time - (Binary64.value final.start + (final.current.elapsed : ℝ))|)) := by
  obtain ⟨signatures, unique, resetMember, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, initialization, _, _, _, _, _, _, _, _, step, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro header objects firstBlock literalBase signed
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program range logger actual rounding floorBound bound heap p buffers before final actions statuses owners
    inPool policy literalFrame stored logging represented trace
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
  obtain ⟨certified, _⟩ := CSRun.logged_trace_correct header objects a.solve.prepareFMI3 signatures pool
    (step.prepared pool made) literalBase firstBlock signed p buffers inPool program range logger actual rounding floorBound
    bound policy reset enterDefined exitDefined heap before final actions statuses owners literalFrame stored logging represented trace
  refine ⟨certified, certified.progress, ?_⟩
  intro observed events after completed
  have same := certified.statuses_eq completed
  subst observed
  have post := certified.completed completed
  exact ⟨rfl, post.1, post.2.2.1, certified.source_observation completed⟩

end Rumoca.FMI3
end
