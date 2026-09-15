import Rumoca.FMI3Float64SetEnvironment
import RumocaFMI3.StateSetterPolicy

/-! Same-source XML permission, generated mode guard and complete actual setter contracts. Other interface selections and full legal-history correspondence remain separate. -/
noncomputable section
namespace Rumoca.FMI3.StateSetterPolicy
open CTree CLiteral

/-- Actual source, XML state identity, mode guard, printed setter fragment
and complete prepared-call contracts share the same compilation product.
The rule concerns this state selection, not full FMI lifecycle compliance. -/
theorem source_permission (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    (∀ state d, Source.Equation a.parsed.ast d ↔
      d a.parsed.ast.state = Binary64.value (ModelExchange.derivative a.solve state)) ∧
    (∃ root, XML.Document root metadata ∧ Float64SetMetadata.Writable root 1 a.parsed.ast.state ∧
      ∀ kind mode, allowed .setStart kind mode = true ↔ Permitted root 1 kind mode) ∧
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
  obtain ⟨compiled, numerical, metadata, derivative, prepared⟩ := float64_set_runtime_source compiled contract
  exact ⟨compiled, numerical, derivative, artifact_modes metadata, prepared⟩

end Rumoca.FMI3.StateSetterPolicy
