import Rumoca.FMI3StateProofs
import RumocaFMI3.StateEnvironment

noncomputable section
namespace Rumoca.FMI3
open CTree CLiteral

/-- Extract the same actual accessor fragments and extend their mandatory
contracts to the common runtime environment, without assuming a later call. -/
theorem adapter_state_environment (contract : AdapterContract a adapter) :
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      (∀ write, ∃ before after : String, adapter = before ++
        (Runtime.function a.solve.prepareFMI3 (StateCalls.signature write)).render ++ after) ∧
      StateCalls.FunctionsContract a.solve.prepareFMI3 sigs
        (fun write => (Runtime.function a.solve.prepareFMI3 (StateCalls.signature write)).render) ∧
      StateEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool := by
  obtain ⟨sigs, unique, _, printed, _, _, _, _, _, ready, _, _, _, _, states, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  refine ⟨sigs, pool, made, printed, ?_, states,
    StateEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique states.member made⟩
  intro write
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 sigs
    (StateCalls.signature write) (states.member write)
  exact ⟨before, after, printed ▸ located⟩

end Rumoca.FMI3
end
