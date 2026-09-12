import Rumoca.FMI3BuildProofs
import RumocaFMI3.LoggingContract

/-! Actual adapter bytes, category metadata and complete enabled failure-helper
calls are tied to one compiled Solve program and its constructed literal pool,
with eventful literal lowering required for the same function table.
The returning host effect and symbolic callback binding are explicit premises
of the required execution contract. Native ABI and whole public APIs remain open. -/
noncomputable section
namespace Rumoca.FMI3
open CTree CLiteral

theorem logging_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Logging.MetadataContract metadata "logStatus" ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      (∃ before text after : String, adapter = before ++ text ++ after ∧
        Logging.FunctionContract a.solve.prepareFMI3 sigs text) ∧
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Logging.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      LiteralPreparation.EventPreparedContract a.solve.prepareFMI3 sigs pool := by
  obtain ⟨sigs, _, _, printed, _, grammar, _, _, _, ready, _, logging, events⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_helper a.solve.prepareFMI3 sigs
    Runtime.helpers[0] (by simp [Runtime.helpers])
  exact ⟨compiled, Logging.metadata_correct _ contract.metadata,
    sigs, pool, printed, grammar, ⟨before, _, after, printed ▸ located, logging⟩,
    made, logging.prepared pool made, events pool made⟩

end Rumoca.FMI3
