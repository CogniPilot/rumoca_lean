import Rumoca.FMI3PublicContracts
import RumocaFMI3.AtomicCallRuntime
import RumocaC.Fenv

/-! Actual-source, printed-function and concrete-header binding for atomic calls in concurrent executions. -/
namespace Rumoca.FMI3.AtomicCallPolicy
open CTree CMemory CCalls CCalls.Events CCallSites RuntimeLinkage

/-- The actual source/adapter certificate supplies the printed function table
and concrete type environment. From ordinary public invocations, every finite
shared-heap execution has the prescribed reservation/release values, without a
separate call-policy, indirect-target or execution-annotation assumption. -/
theorem source_atomic_calls (compiled : compile input = .ok a)
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
            (∀ thread args heap stack,
              after.threads thread = some (.calling "atomic_exchange" args heap stack) →
              ∃ pointer, args = [pointer, CAtomicBoolean.value true]) ∧
            (∀ thread args heap stack,
              after.threads thread = some (.calling "atomic_store" args heap stack) →
              ∃ pointer, args = [pointer, CAtomicBoolean.value false]) := by
  obtain ⟨sigs, rendered, functions, prepared, covered, _⟩ := adapter_public_contracts contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp prepared
  refine ⟨compiled, contract.numerical, CapabilityMetadata.artifact _ _ contract.metadata,
    sigs, pool, made, rendered, functions, covered, ?_⟩
  intro header instances flags separate firstBlock
  let objects := StaticRuntime.objects instances flags separate
  letI : CInterface := header.interface (StaticFactory.executionInterface objects (pool.addresses firstBlock))
  dsimp only
  intro tag observed range logger environment effect
  let program := logged a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl observed range logger effect
  obtain ⟨actual, callback, _, _, statics, floor, rounding⟩ :=
    logged_contract a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl observed range logger environment effect
  refine ⟨program, actual, callback, statics, floor, rounding, ?_⟩
  intro before after entries path
  have ready := logged_concurrent_reaches a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl
    observed range logger effect before after entries path
  exact ⟨fun _ _ _ _ calling => exchange_value ready calling,
    fun _ _ _ _ calling => release_value ready calling⟩

end Rumoca.FMI3.AtomicCallPolicy
