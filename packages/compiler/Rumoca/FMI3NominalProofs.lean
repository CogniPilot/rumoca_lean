import Rumoca.FMI3BuildProofs
import RumocaFMI3.NominalContract
import RumocaFMI3.NominalMetadata

/-! The actual adapter fragment, ordered XML state and complete nominal query
share the compiled source/Solve and literal-pool witnesses. Native ABI,
allocation and admissible-host correspondence remain separate obligations. -/
noncomputable section
namespace Rumoca.FMI3
open CTree CLiteral

theorem nominals_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ NominalMetadata.Contract a.parsed.ast metadata ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      (∃ before text after : String, adapter = before ++ text ++ after ∧
        Nominals.FunctionContract a.solve.prepareFMI3 sigs text) ∧
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Nominals.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      LiteralPreparation.EventPreparedContract a.solve.prepareFMI3 sigs pool := by
  obtain ⟨sigs, _, _, printed, _, grammar, _, _, _, ready, _, _, events, nominals⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 sigs
    ErrorCalls.nominalSignature nominals.member
  exact ⟨compiled, NominalMetadata.artifact_nominals _ _ contract.metadata, sigs, pool, printed, grammar,
    ⟨before, _, after, printed ▸ located, nominals⟩, made, nominals.prepared pool made, events pool made⟩

end Rumoca.FMI3
