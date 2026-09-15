import Rumoca.FMI3PublicContracts
import RumocaFMI3.HostCallPolicy
import RumocaC.Fenv

namespace Rumoca.FMI3.AtomicCallPolicy
open CTree CMemory CCalls CCalls.Events CCallSites RuntimeLinkage

/-- The actual source/adapter contract supplies the program and public entry
table for repeated host invocations. Actual C execution remains unchanged;
explicit host memory effects are unrestricted for this control-only theorem.
Lease provenance, buffer frames and complete lifecycle behavior are separate. -/
theorem source_host_calls (compiled : compile input = .ok a)
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
          ∀ (domain : Concurrent.State → Nat → Signature → List Value → Prop)
            (memory : Concurrent.State → Nat → Heap → Prop),
            ∀ heap trace after,
            Host.History program (Host.publicPolicy sigs domain memory) ⟨heap, fun _ => none⟩ trace after →
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
  intro domain memory heap trace after path
  have ready := logged_host_history a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl
    observed range logger effect domain memory heap trace after path
  exact ⟨fun _ _ _ _ calling => exchange_value ready calling,
    fun _ _ _ _ calling => release_value ready calling⟩

end Rumoca.FMI3.AtomicCallPolicy
