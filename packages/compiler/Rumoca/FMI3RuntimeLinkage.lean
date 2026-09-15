import Rumoca.FMI3PublicContracts
import RumocaFMI3.RuntimeLinkage
import RumocaC.Fenv

/-! The actual source/adapter contract constructs the concrete literal, type and runtime environment used by the call-depth theorem. -/
noncomputable section
namespace Rumoca.FMI3.RuntimeLinkage
open CTree CMemory CCalls CCalls.Events CCallPolicy

/-- Source, numerical C, actual adapter bytes, public printers and the
constructed literal pool supply the concrete object/fenv interface. Its complete
library/logger environment has the proved all-prefix call-depth bound. No
separate type-binding, pointer-policy or rank premise is required. Native
layout, library implementations and callback internals remain external. -/
theorem source_logged_environment
    (compiled : compile input = .ok a)
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
          (∀ name fn, StaticRuntime.library tag rfl rfl rfl name = some fn →
            program.externals name = some fn) ∧
          program.externals "floor" = some (CMathCalls.floorExternal rfl) ∧
          program.externals "fegetround" = some (CMathCalls.roundingExternal rfl observed range) ∧
          ∀ entry args before events target,
            Transition.Events.Reaches (Events.machine program).step
              (.calling entry args before .done) events target → CCallDepth.stateDepth target ≤ 3 := by
  obtain ⟨sigs, rendered, functions, ready, covered, _⟩ := adapter_public_contracts contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
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
  exact ⟨program, actual, callback, statics, floor, rounding,
    logged_execution_depth a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl observed range logger effect⟩

end Rumoca.FMI3.RuntimeLinkage
