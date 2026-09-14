import Rumoca.FMI3Float64SetProofs
import RumocaFMI3.Float64SetEnvironment

noncomputable section
namespace Rumoca.FMI3
open CTree CLiteral

/-- Source compilation, numerical C, writable-state metadata and the actual
setter fragment supply complete Float64 writes in the shared static runtime.
The same prepared pool covers later read-only-preserving heaps and all
represented callback outcomes. Interleaved initialization histories remain a
separate composition obligation. -/
theorem float64_set_runtime_source (compiled : compile input = .ok a)
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
      Float64SetEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool := by
  obtain ⟨sigs, unique, _, printed, _, grammar, _, _, _, ready, _, _, _, _, _, _, _, setter, _⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 sigs
    (Float64Calls.signature true) setter.member
  exact ⟨compiled, contract.numerical, Float64SetMetadata.artifact_state _ _ contract.metadata,
    derivative_value_source a.solve, sigs, pool, printed, grammar,
    ⟨before, after, printed ▸ located⟩, setter, made, setter.prepared pool made,
    Float64SetEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique setter.member made⟩

end Rumoca.FMI3
end
