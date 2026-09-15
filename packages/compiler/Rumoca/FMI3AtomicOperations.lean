import Rumoca.FMI3AtomicCalls
import RumocaFMI3.AtomicCallExecution

/-! Actual-source/artifact consequences for atomic effects after finite concurrent execution. -/
namespace Rumoca.FMI3.AtomicCallPolicy
open CTree CMemory CCalls CCalls.Events RuntimeLinkage

/-- Same-source artifact and concrete type/linkage contracts derive actual
atomic operation effects after arbitrary finite shared execution from public
entries. Neither converted arguments nor later call annotations are premises. -/
theorem source_atomic_operations (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    CapabilityMetadata.ArtifactContract metadata ∧
    ∃ sigs, ∃ pool : CLiteral.Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap CLiteral.functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      PublicAPI.Covered sigs ∧
      ∀ (header : CFenv.Header) (instances flags : Nat) (separate : instances ≠ flags) (firstBlock : Nat),
        let objects := StaticRuntime.objects instances flags separate
        letI : CInterface := header.interface (StaticFactory.executionInterface objects (pool.addresses firstBlock))
        ∀ (tag : CAtomicBoolean.Calls.Event → Invocation)
          (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
          (logger : Address) (environment : Option Address)
          (effect : ReturningEffect (Logging.signature hostName)),
        ∃ program : Events.Program Invocation,
          program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs ∧
          (Logging.Capability.present logger environment hostName effect).Bound program ∧
          (∀ name fn, StaticRuntime.library tag rfl rfl rfl name = some fn → program.externals name = some fn) ∧
          program.externals "floor" = some (CMathCalls.floorExternal rfl) ∧
          program.externals "fegetround" = some (CMathCalls.roundingExternal rfl observed range) ∧
          ∀ (before after : Concurrent.State),
            (∀ thread saved, before.threads thread = some saved →
              ∃ sig ∈ sigs, ∃ args heap, saved = .calling sig.name args heap .done) →
            Transition.Reaches (fun a b => ∃ thread events, Concurrent.Step program a thread events b) before after →
            OperationalCalls program tag after := by
  obtain ⟨compiled, numerical, metadata, sigs, pool, prepared, rendered, functions, covered, environment⟩ :=
    source_atomic_calls compiled contract
  refine ⟨compiled, numerical, metadata, sigs, pool, prepared, rendered, functions, covered, ?_⟩
  intro header instances flags separate firstBlock
  let objects := StaticRuntime.objects instances flags separate
  letI : CInterface := header.interface (StaticFactory.executionInterface objects (pool.addresses firstBlock))
  dsimp only
  intro tag observed range logger hostEnvironment effect
  obtain ⟨program, actual, callback, library, floor, rounding, values⟩ :=
    environment header instances flags separate firstBlock tag observed range logger hostEnvironment effect
  refine ⟨program, actual, callback, library, floor, rounding, ?_⟩
  intro before after entries path
  obtain ⟨exchangeValues, releaseValues⟩ := values before after entries path
  exact operations_of_values program tag rfl rfl (library "atomic_exchange" _ rfl)
    (library "atomic_store" _ rfl) exchangeValues releaseValues

end Rumoca.FMI3.AtomicCallPolicy
