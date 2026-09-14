import Rumoca.FMI3DerivativeProofs
import RumocaFMI3.StateEnvironment
import RumocaFMI3.DerivativeEnvironment

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CLiteral StaticFactory

/-- State access, derivative access and the shared numerical helper belong
to one actual function table and pool, ready for mixed ME histories. -/
theorem adapter_me_numerical_environment (contract : AdapterContract a adapter) :
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      (∀ write, ∃ before after : String, adapter = before ++
        (Runtime.function a.solve.prepareFMI3 (StateCalls.signature write)).render ++ after) ∧
      (∃ before after : String, adapter = before ++
        (Runtime.function a.solve.prepareFMI3 DerivativeCalls.signature).render ++ after) ∧
      (∃ before after : String, adapter = before ++ Runtime.helpers[1].render ++ after) ∧
      StateCalls.FunctionsContract a.solve.prepareFMI3 sigs
        (fun write => (Runtime.function a.solve.prepareFMI3 (StateCalls.signature write)).render) ∧
      DerivativeCalls.FunctionContract a.solve.prepareFMI3 sigs
        (Runtime.function a.solve.prepareFMI3 DerivativeCalls.signature).render Runtime.helpers[1].render ∧
      StateEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      DerivativeEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool := by
  obtain ⟨sigs, unique, _, printed, _, _, _, _, _, ready, _, _, _, _, states, derivative, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 sigs
    DerivativeCalls.signature derivative.member
  obtain ⟨helperBefore, helperAfter, helperLocated⟩ := LiteralPreparation.rendered_helper a.solve.prepareFMI3 sigs
    Runtime.helpers[1] (by simp [Runtime.helpers])
  refine ⟨sigs, pool, made, printed, ?_, ⟨before, after, printed ▸ located⟩,
    ⟨helperBefore, helperAfter, printed ▸ helperLocated⟩, states, derivative,
    StateEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique states.member made,
    DerivativeEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique derivative.member
      derivative.numerical.fresh made⟩
  intro write
  obtain ⟨stateBefore, stateAfter, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 sigs
    (StateCalls.signature write) (states.member write)
  exact ⟨stateBefore, stateAfter, printed ▸ located⟩

/-- Actual source, numerical C and derivative/state metadata share the same
runtime call. Valid caller output storage is explicit; no derivative-call
execution, post-call heap, or importer trajectory is an input premise. -/
theorem runtime_derivative_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    DerivativeMetadata.Contract a.parsed.ast metadata ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      StateEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      DerivativeEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
        letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program E),
          program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs →
          ∀ (heap : Heap) (p buffer : Address) (mode : Mode) (state : ModelExchange.State) (old : Option Value),
          load heap (p.member "kind") = some (.integer 0) →
          load heap (p.member "mode") = some (.integer mode.code) →
          Reference.Allowed .getDerivatives .me mode → heap buffer = some ⟨.float64, true, old⟩ →
          ∃ after derivative,
            derivative = ModelExchange.derivative a.solve state ∧
            (∀ behavior, (CCalls.Events.machine program).Behaves
              (.calling DerivativeCalls.signature.name
                (DerivativeCalls.values (some p) (some buffer) 1) heap .done) behavior ↔
              behavior = .terminates [] ⟨.integer 0, after⟩) ∧
            load after buffer = some (.finite derivative) ∧
            (∀ d : String → ℝ, Source.Equation a.parsed.ast d ↔
              d a.parsed.ast.state = Binary64.value derivative) ∧
            (∀ query, query ≠ buffer → after query = heap query) := by
  obtain ⟨sigs, pool, made, printed, _, _, _, _, _, statePrepared, prepared⟩ := adapter_me_numerical_environment contract.adapter
  refine ⟨compiled, contract.numerical, DerivativeMetadata.artifact_derivatives _ _ contract.metadata,
    sigs, pool, made, printed, statePrepared, prepared, ?_⟩
  intro header E objects firstBlock
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual heap p buffer mode state old hk hm allowed storage
  obtain ⟨after, called, loaded, frame, _⟩ :=
    (prepared.quiet header E objects firstBlock program actual heap).get_refines
      p buffer mode state old hk hm allowed storage
  exact ⟨after, ModelExchange.derivative a.solve state, rfl, called, loaded,
    derivative_value_source a.solve state, frame⟩

end Rumoca.FMI3
end
