import Rumoca.FMI3BuildProofs
import RumocaFMI3.DerivativeContract
import RumocaFMI3.DerivativeMetadata

noncomputable section
namespace Rumoca.FMI3

/-- The exposed finite derivative denotes exactly the Real derivative required
by the source equation, composing the existing Flat, DAE and Solve relations. -/
theorem derivative_value_source (model : Solve.Model source) (state : ModelExchange.State) (d : String → ℝ) :
    Source.Equation source d ↔
      d source.state = Binary64.value (ModelExchange.derivative model state) := by
  rw [flatten_correct model.dae.flat, ← dae_correct model.dae, solve_correct model,
    model.rhs_eq_one, ModelExchange.derivative_correct, Binary64.value_one]
  simp

/-- The public output write refines the source Real equation. The derivative
call contract remains an explicit premise here; the actual-artifact wrapper
must obtain it from the mandatory adapter contract for the same function table. -/
theorem derivative_call_source [interface : CInterface]
    (model : Solve.FMI3Model source) (program : CCalls.Events.Program E) (heap : CMemory.Heap)
    (contract : DerivativeCalls.QuietExecutionContract model program heap)
    (p buffer : CMemory.Address) (mode : Mode) (state : ModelExchange.State) (old : Option CMemory.Value)
    (hk : CMemory.load heap (p.member "kind") = some (.integer 0))
    (hm : CMemory.load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives .me mode)
    (storage : heap buffer = some ⟨.float64, true, old⟩) :
    ∃ after derivative,
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling DerivativeCalls.signature.name
          (DerivativeCalls.values (some p) (some buffer) 1) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, after⟩) ∧
      CMemory.load after buffer = some (.finite derivative) ∧
      (∀ d : String → ℝ, Source.Equation source d ↔ d source.state = Binary64.value derivative) ∧
      (∀ address, address ≠ buffer → after address = heap address) := by
  obtain ⟨after, behaviors, loaded, frame, _⟩ := contract.get_refines p buffer mode state old hk hm allowed storage
  exact ⟨after, ModelExchange.derivative model.solve state, behaviors, loaded,
    derivative_value_source model.solve state, frame⟩

end Rumoca.FMI3

noncomputable section
namespace Rumoca.FMI3
open CTree CLiteral

/-- The actual numerical and adapter bytes, derivative order and complete
public/helper call contracts belong to one compiled source and prepared Solve
model. The same literal pool carries the mandatory event-preservation proof.
Native headers/ABI, importer storage and host realization remain boundaries. -/
theorem derivative_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    DerivativeMetadata.Contract a.parsed.ast metadata ∧
    (∀ state d, Source.Equation a.parsed.ast d ↔
      d a.parsed.ast.state = Binary64.value (ModelExchange.derivative a.solve state)) ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      (∃ before after : String, adapter = before ++
        (Runtime.function a.solve.prepareFMI3 DerivativeCalls.signature).render ++ after) ∧
      (∃ before after : String, adapter = before ++ Runtime.helpers[1].render ++ after) ∧
      DerivativeCalls.FunctionContract a.solve.prepareFMI3 sigs
        (Runtime.function a.solve.prepareFMI3 DerivativeCalls.signature).render Runtime.helpers[1].render ∧
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      DerivativeCalls.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      LiteralPreparation.EventPreparedContract a.solve.prepareFMI3 sigs pool := by
  obtain ⟨sigs, _, _, printed, _, grammar, _, _, _, ready, _, _, events, _, _, derivative⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 sigs
    DerivativeCalls.signature derivative.member
  obtain ⟨helperBefore, helperAfter, helperLocated⟩ := LiteralPreparation.rendered_helper a.solve.prepareFMI3 sigs
    Runtime.helpers[1] (by simp [Runtime.helpers])
  exact ⟨compiled, contract.numerical, DerivativeMetadata.artifact_derivatives _ _ contract.metadata,
    derivative_value_source a.solve, sigs, pool, printed, grammar,
    ⟨before, after, printed ▸ located⟩, ⟨helperBefore, helperAfter, printed ▸ helperLocated⟩,
    derivative, made, derivative.prepared pool made, events pool made⟩

end Rumoca.FMI3
