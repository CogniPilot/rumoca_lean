import Rumoca.FMI3BuildProofs
import RumocaFMI3.AbsentVariableMetadata

noncomputable section
namespace Rumoca.FMI3
open CTree CLiteral

/-- The same compiled source supplies the numerical C, actual XML absence,
all 24 printed accessors and their common prepared program/literal pool.
The raw execution contracts include defensive calls outside legal importer
histories; XML absence does not relax lifecycle or pointer requirements. -/
theorem absent_variables_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    AbsentVariables.MetadataContract metadata ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      ∀ ty write,
        (∃ before text after : String, adapter = before ++ text ++ after ∧
          AbsentVariables.FunctionContract a.solve.prepareFMI3 sigs ty write text) ∧
        AbsentVariables.PreparedContract a.solve.prepareFMI3 sigs ty write pool := by
  obtain ⟨sigs, _, _, printed, _, grammar, _, _, _, ready,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, family, _⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  refine ⟨compiled, contract.numerical, AbsentVariables.artifact_absence _ _ contract.metadata,
    sigs, pool, made, printed, grammar, ?_⟩
  intro ty write
  have query := family ty write
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 sigs
    (AbsentVariables.signature ty write) query.member
  exact ⟨⟨before, _, after, printed ▸ located, query⟩, query.prepared pool made⟩

end Rumoca.FMI3
end
