import Rumoca.FMI3Float64Proofs
import RumocaFMI3.Float64SetContract

noncomputable section
namespace Rumoca.FMI3
open CTree CLiteral

/-- The actual public setter, writable XML state and complete call contracts
share one source, prepared Solve model, function table and literal pool. The
setter preserves accepted payload bits and refines the semantic state update.
Allocation, initialization histories and native ABI/ownership remain separate. -/
theorem float64_set_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    Float64SetMetadata.Contract a.parsed.ast metadata ∧
    (∀ state d, Source.Equation a.parsed.ast d ↔
      d a.parsed.ast.state = Binary64.value (ModelExchange.derivative a.solve state)) ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      (∃ before after : String, adapter = before ++
        (Runtime.function a.solve.prepareFMI3 (Float64Calls.signature true)).render ++ after) ∧
      Float64Set.FunctionContract a.solve.prepareFMI3 sigs
        (Runtime.function a.solve.prepareFMI3 (Float64Calls.signature true)).render ∧
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Float64Set.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      LiteralPreparation.EventPreparedContract a.solve.prepareFMI3 sigs pool := by
  obtain ⟨sigs, _, _, printed, _, grammar, _, _, _, ready, _, _, events, _, _, _, _, setter, _⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 sigs
    (Float64Calls.signature true) setter.member
  exact ⟨compiled, contract.numerical, Float64SetMetadata.artifact_state _ _ contract.metadata,
    derivative_value_source a.solve, sigs, pool, printed, grammar,
    ⟨before, after, printed ▸ located⟩, setter, made, setter.prepared pool made, events pool made⟩

end Rumoca.FMI3
