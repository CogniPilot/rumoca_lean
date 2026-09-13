import Rumoca.FMI3BuildProofs
import RumocaFMI3.StateContract
import RumocaFMI3.StateMetadata

/-! Actual getter/setter bytes, XML state ordering and complete public-call
semantics are required for the same compiled source, Solve model, function
table and literal pool. Importer storage, native ABI and callback realization
remain explicit boundaries; setting a state does not prove a solver trajectory. -/
noncomputable section
namespace Rumoca.FMI3
open CTree CLiteral

theorem state_access_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ StateMetadata.Contract a.parsed.ast metadata ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      (∀ write, ∃ before after : String, adapter = before ++
        (Runtime.function a.solve.prepareFMI3 (StateCalls.signature write)).render ++ after) ∧
      StateCalls.FunctionsContract a.solve.prepareFMI3 sigs
        (fun write => (Runtime.function a.solve.prepareFMI3 (StateCalls.signature write)).render) ∧
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      StateCalls.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      LiteralPreparation.EventPreparedContract a.solve.prepareFMI3 sigs pool := by
  obtain ⟨sigs, _, _, printed, _, grammar, _, _, _, ready, _, _, events, _, states⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  refine ⟨compiled, StateMetadata.artifact_states _ _ contract.metadata,
    sigs, pool, printed, grammar, ?_, states, made, states.prepared pool made, events pool made⟩
  intro write
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 sigs
    (StateCalls.signature write) (states.member write)
  exact ⟨before, after, printed ▸ located⟩

end Rumoca.FMI3
