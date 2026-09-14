import Rumoca.FMI3Float64SetEnvironment
import RumocaFMI3.Float64Environment

noncomputable section
namespace Rumoca.FMI3
open CTree CLiteral

/-- Both Float64 accessors and the RHS helper share actual source compilation,
numerical C, XML reference/state metadata and one prepared runtime table/pool.
The getter's derivative denotes the source Real equation; its current time/state
and the setter's selected state are governed by their complete call contracts.
Interleaved initialization/lifetime histories remain separate obligations. -/
theorem float64_runtime_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    Float64Metadata.Contract a.solve.prepareFMI3 metadata ∧
    Float64SetMetadata.Contract a.parsed.ast metadata ∧
    (∀ state d, Source.Equation a.parsed.ast d ↔
      d a.parsed.ast.state = Binary64.value (ModelExchange.derivative a.solve state)) ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      (∀ write, ∃ before after : String, adapter = before ++
        (Runtime.function a.solve.prepareFMI3 (Float64Calls.signature write)).render ++ after) ∧
      (∃ before after : String, adapter = before ++ Runtime.helpers[1].render ++ after) ∧
      Float64Calls.FunctionContract a.solve.prepareFMI3 sigs
        (Runtime.function a.solve.prepareFMI3 (Float64Calls.signature false)).render Runtime.helpers[1].render ∧
      Float64Set.FunctionContract a.solve.prepareFMI3 sigs
        (Runtime.function a.solve.prepareFMI3 (Float64Calls.signature true)).render ∧
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Float64Environment.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      Float64SetEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool := by
  obtain ⟨sigs, unique, _, printed, _, grammar, _, _, _, ready, _, _, _, _, _, _, getter, setter, _⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  obtain ⟨helperBefore, helperAfter, helperLocated⟩ := LiteralPreparation.rendered_helper a.solve.prepareFMI3 sigs
    Runtime.helpers[1] (by simp [Runtime.helpers])
  refine ⟨compiled, contract.numerical, Float64Metadata.artifact_variables _ _ contract.metadata,
    Float64SetMetadata.artifact_state _ _ contract.metadata, derivative_value_source a.solve,
    sigs, pool, printed, grammar, ?_, ⟨helperBefore, helperAfter, printed ▸ helperLocated⟩,
    getter, setter, made,
    Float64Environment.prepared_correct a.solve.prepareFMI3 sigs unique getter.member getter.numerical.fresh made,
    Float64SetEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique setter.member made⟩
  intro write
  have member : Float64Calls.signature write ∈ sigs := by
    cases write
    · exact getter.member
    · exact setter.member
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 sigs
    (Float64Calls.signature write) member
  exact ⟨before, after, printed ▸ located⟩

end Rumoca.FMI3
end
