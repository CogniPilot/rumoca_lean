import Rumoca.FMI3PublicContracts
import RumocaFMI3.FactoryAfterScan
import RumocaC.Fenv

namespace Rumoca.FMI3.ReservationOrigin
open CTree CMemory CCalls CCalls.Events RuntimeLinkage

/-- The source and actual adapter certificate supply the program for the
post-scan factory history. Both success and capacity exhaustion retain the
closed suffix: this public invocation cannot reserve a second slot. -/
theorem source_factory_suffix (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    CapabilityMetadata.ArtifactContract metadata ∧
    ∃ sigs, ∃ pool : CLiteral.Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap CLiteral.functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧ PublicAPI.Covered sigs ∧
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
          ∀ (kind : Kind) (value : Value) (heap : Heap) (env : CBody.Locals) (types : CLoops.Types)
            (before after : Concurrent.State) (tracked : Nat),
            before.threads tracked = some (.returning value heap
              (.caller (.declare "size_t" "slot")
                (StaticFactory.guard :: StaticFactory.initializeInstance a.solve.prepareFMI3.solve kind)
                env types "fmi3Instance" .done)) →
            Transition.Reaches (fun s t => ∃ thread effects, Concurrent.Step program s thread effects t) before after →
            ∀ name args savedHeap stack, after.threads tracked = some (.calling name args savedHeap stack) → allowed name = true := by
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
  exact logged_factory_suffix a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl observed range logger effect

end Rumoca.FMI3.ReservationOrigin
