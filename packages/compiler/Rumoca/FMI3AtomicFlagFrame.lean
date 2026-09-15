import Rumoca.FMI3PublicContracts
import RumocaFMI3.AtomicFlagFrame
import RumocaC.Fenv

/-! Same-source actual-runtime atomic flag frames and attribution of changes. -/
namespace Rumoca.FMI3.AtomicFlagFrame
open CTree CMemory CCalls CCalls.Events RuntimeLinkage

/-- The source contract constructs the same prepared runtime. Callback flag
stability yields ordinary-step framing; without that assumption, every change
is attributed to an actual atomic or importer call. No per-step annotations
or additional type/library bindings are premises. -/
theorem source_flag_frames (compiled : compile input = .ok a)
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
          ((∀ args before result after, effect.execute args before result after →
              CAtomicBoolean.Preserves before after) →
            ∀ before thread events after, Concurrent.Step program before thread events after →
              CAtomicBoolean.Preserves before.heap after.heap ∨
                ∃ saved name args stack, before.threads thread = some saved ∧
                  Concurrent.withHeap saved before.heap = .calling name args before.heap stack ∧
                  AtomicRoutine name) ∧
          (∀ before thread events after, Concurrent.Step program before thread events after →
            ¬ CAtomicBoolean.Preserves before.heap after.heap →
              ∃ saved name args stack, before.threads thread = some saved ∧
                Concurrent.withHeap saved before.heap = .calling name args before.heap stack ∧
                (AtomicRoutine name ∨ name = hostName)) := by
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
  refine ⟨program, actual, callback, statics, floor, rounding, ?_, ?_⟩
  · exact fun callback => logged_step a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl
      observed range logger effect callback
  · exact logged_changed_origin a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl
      observed range logger effect

end Rumoca.FMI3.AtomicFlagFrame
