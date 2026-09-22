import Rumoca.FMI3BuildProofs
import RumocaFMI3.DiscreteEvaluationMetadata

noncomputable section
namespace Rumoca.FMI3
open CTree CLiteral

/-- Actual C and XML bind the no-op call to the same compiled Solve product.
The capability's omitted/false default is explicit in the metadata relation.
The runtime supplies all represented successes and failures on each valid
later heap; neither a chosen result nor a successful logger is a premise. -/
theorem discrete_evaluation_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    DiscreteEvaluation.MetadataContract metadata ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      (∃ before text after : String, adapter = before ++ text ++ after ∧
        DiscreteEvaluation.FunctionContract a.solve.prepareFMI3 sigs text) ∧
      DiscreteEvaluation.PreparedContract a.solve.prepareFMI3 sigs pool := by
  obtain ⟨sigs, _, _, printed, _, grammar, _, _, _, ready,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, query, _⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 sigs
    DiscreteEvaluation.signature query.member
  exact ⟨compiled, contract.numerical, DiscreteEvaluation.artifact_capability _ _ contract.metadata,
    sigs, pool, made, printed, grammar, ⟨before, _, after, printed ▸ located, query⟩,
    query.prepared pool made⟩

end Rumoca.FMI3
end
