import Rumoca.FMI3PublicContracts
import RumocaFMI3.RuntimeStorage
import RumocaC.Fenv

/-! Source and actual adapter contracts construct one runtime environment with modeled call-depth and storage guarantees. Native resource behavior remains external. -/
noncomputable section
namespace Rumoca.FMI3.RuntimeStorage
open CTree CMemory CCalls CCalls.Events CStoreInvariant CStorage RuntimeLinkage

/-- Actual source and artifact contracts construct one environment with
bounded modeled calls and explicit storage consequences. No new callback
premise is imposed on the accepted artifact: preservation is conditional, while
attribution of any storage change to an executed callback is unconditional. -/
theorem source_resource_environment
    (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c descriptionXml adapter metadata) :
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
          (∀ entry args before events target,
            Transition.Events.Reaches (Events.machine program).step
              (.calling entry args before .done) events target → CCallDepth.stateDepth target ≤ 3) ∧
          ((∀ args before result after, effect.execute args before result after → Preserves before after) →
            ∀ s events t, Transition.Events.Reaches (Events.machine program).step s events t →
              Preserves (CReadOnly.typedHeap s) (CReadOnly.typedHeap t)) ∧
          (∀ s events t, Transition.Events.Reaches (Events.machine program).step s events t →
            ¬ Preserves (CReadOnly.typedHeap s) (CReadOnly.typedHeap t) →
            ∃ preEvents suffix args values before result after stack,
              Transition.Events.Reaches (Events.machine program).step s preEvents
                (.calling hostName args before stack) ∧
              convertedArguments (Logging.signature hostName).parameters args = some values ∧
              effect.execute values before result after ∧ ¬ Preserves before after ∧
              Transition.Events.Reaches (Events.machine program).step
                (.returning result after stack) suffix t ∧
              events = preEvents ++ [⟨hostName, values⟩] ++ suffix) := by
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
  refine ⟨program, actual, callback, statics, floor, rounding,
    logged_execution_depth a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl observed range logger effect, ?_,
    logged_change_origin a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl observed range logger effect⟩
  intro preserves s events t path
  exact event_reaches stable Preserves.trans
    (logged_storage a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl observed range logger effect preserves) path

end Rumoca.FMI3.RuntimeStorage
