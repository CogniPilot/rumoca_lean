import Rumoca.FMI3BuildProofs
import RumocaFMI3.CapabilityMetadata

namespace Rumoca.FMI3
noncomputable section
open CTree CLiteral

/-- The added family shares the actual compiled source, printed adapter,
numerical C, XML, definition table and diagnostic pool. Legal importer histories
and full native header/ABI correspondence are separate obligations. -/
theorem capabilities_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    CapabilityMetadata.ArtifactContract metadata ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      ∀ sig ∈ CapabilityRejection.signatures,
        (∃ before text after : String, adapter = before ++ text ++ after ∧
          CapabilityRejection.FunctionContract a.solve.prepareFMI3 sigs sig sig.parameters.tail text) ∧
        CapabilityRejection.PreparedContract a.solve.prepareFMI3 sigs sig sig.parameters.tail pool := by
  obtain ⟨sigs, _, _, printed, _, grammar, _, _, _, ready,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, family⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  refine ⟨compiled, contract.numerical, CapabilityMetadata.artifact _ _ contract.metadata,
    sigs, pool, made, printed, grammar, ?_⟩
  intro sig member
  have query := family.family sig member
  obtain ⟨before, after, located⟩ := query.fragment
  exact ⟨⟨before, _, after, printed ▸ located, query⟩, query.prepared pool made⟩

/-- Unsupported scheduled creation is certified in the same source artifact
and prepared literal pool as the ME/CS numerical kernel and public APIs. -/
theorem scheduled_creation_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    CapabilityMetadata.ArtifactContract metadata ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      (∃ before text after : String, adapter = before ++ text ++ after ∧
        ScheduledCreation.FunctionContract a.solve.prepareFMI3 sigs text) ∧
      ScheduledCreation.PreparedContract a.solve.prepareFMI3 sigs pool := by
  obtain ⟨sigs, _, _, printed, _, grammar, _, _, _, ready,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, family⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  have query := family.scheduled
  obtain ⟨before, after, located⟩ := query.fragment
  exact ⟨compiled, contract.numerical, CapabilityMetadata.artifact _ _ contract.metadata,
    sigs, pool, made, printed, grammar, ⟨before, _, after, printed ▸ located, query⟩,
    query.prepared pool made⟩

end
end Rumoca.FMI3
