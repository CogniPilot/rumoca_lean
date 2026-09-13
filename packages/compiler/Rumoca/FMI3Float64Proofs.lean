import Rumoca.FMI3DerivativeProofs
import RumocaFMI3.Float64Contract

noncomputable section
namespace Rumoca.FMI3
open CTree CLiteral

/-- The actual Float64 getter and RHS helper, XML reference map and complete
call contracts belong to the same source, prepared Solve model, function table
and literal pool. Their numerical derivative denotes the source Real equation.
Initial/current state and time still require the admitted heap representation;
native ABI, ownership and complete initialization remain explicit boundaries. -/
theorem float64_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    Float64Metadata.Contract a.solve.prepareFMI3 metadata ∧
    (∀ state d, Source.Equation a.parsed.ast d ↔
      d a.parsed.ast.state = Binary64.value (ModelExchange.derivative a.solve state)) ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      (∃ before after : String, adapter = before ++
        (Runtime.function a.solve.prepareFMI3 (Float64Calls.signature false)).render ++ after) ∧
      (∃ before after : String, adapter = before ++ Runtime.helpers[1].render ++ after) ∧
      Float64Calls.FunctionContract a.solve.prepareFMI3 sigs
        (Runtime.function a.solve.prepareFMI3 (Float64Calls.signature false)).render Runtime.helpers[1].render ∧
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Float64Calls.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      LiteralPreparation.EventPreparedContract a.solve.prepareFMI3 sigs pool := by
  obtain ⟨sigs, _, _, printed, _, grammar, _, _, _, ready, _, _, events, _, _, _, float64, _⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 sigs
    (Float64Calls.signature false) float64.member
  obtain ⟨helperBefore, helperAfter, helperLocated⟩ := LiteralPreparation.rendered_helper a.solve.prepareFMI3 sigs
    Runtime.helpers[1] (by simp [Runtime.helpers])
  exact ⟨compiled, contract.numerical, Float64Metadata.artifact_variables _ _ contract.metadata,
    derivative_value_source a.solve, sigs, pool, printed, grammar,
    ⟨before, after, printed ▸ located⟩, ⟨helperBefore, helperAfter, printed ▸ helperLocated⟩,
    float64, made, float64.prepared pool made, events pool made⟩

end Rumoca.FMI3
