import Rumoca.FMI3BuildProofs
import RumocaFMI3.DebugLoggingContract

/-! Actual source, numerical C, XML categories and the public logging fragment
share the prepared Solve product and definition/literal witnesses. Native ABI
and mutable-policy host histories remain separate obligations. -/
noncomputable section
namespace Rumoca.FMI3
open CTree CLiteral

theorem debug_logging_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    DebugLogging.MetadataContract metadata "logStatus" ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      (∃ before text after : String, adapter = before ++ text ++ after ∧
        DebugLogging.FunctionContract a.solve.prepareFMI3 sigs text) ∧
      DebugLogging.PreparedContract a.solve.prepareFMI3 sigs pool := by
  obtain ⟨sigs, _, _, printed, _, grammar, _, _, _, ready,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, logging, _⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 sigs
    DebugLogging.signature logging.member
  exact ⟨compiled, contract.numerical, DebugLogging.artifact_category _ _ contract.metadata,
    sigs, pool, made, printed, grammar, ⟨before, _, after, printed ▸ located, logging⟩,
    logging.prepared pool made⟩

end Rumoca.FMI3
end
