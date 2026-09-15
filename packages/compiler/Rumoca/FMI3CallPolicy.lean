import Rumoca.FMI3PublicContracts
import RumocaFMI3.CallPolicy

/-! Derive call classification and complete direct-call acyclicity from the mandatory actual-source/adapter contract. -/
namespace Rumoca.FMI3.CallPolicy
open CTree CCallPolicy

/-- This consequence uses the mandatory contract for the independently read
adapter. It classifies and ranks all rendered tree calls, retaining foreign,
indirect and native boundaries. -/
theorem actual_adapter_policy (contract : AdapterContract a adapter) :
    ∃ sigs, Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      PublicAPI.Covered sigs ∧
      (∀ fn ∈ LiteralPreparation.functions a.solve.prepareFMI3 sigs,
        checkFunction accepted fn = true) ∧
      checkRanks functionRank (LiteralPreparation.functions a.solve.prepareFMI3 sigs) = true := by
  obtain ⟨sigs, printed, _, _, covered, _⟩ := adapter_public_contracts contract
  exact ⟨sigs, printed, covered, functions_policy a.solve.prepareFMI3 sigs,
    functions_rank a.solve.prepareFMI3 sigs (covered_ranks covered)⟩

/-- Numerical correctness, complete call classification and the direct-call
ranking concern the same source, emitted adapter and prepared function table.
This does not assert native no-heap behavior or exclude callback reentry. -/
theorem source_program_policy (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    ∃ sigs, Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      PublicAPI.Covered sigs ∧
      (∀ fn ∈ LiteralPreparation.functions a.solve.prepareFMI3 sigs,
        checkFunction accepted fn = true) ∧
      ProgramRanked functionRank (LiteralPreparation.program a.solve.prepareFMI3 sigs) ∧
      ∀ caller callee, ProgramEdge (LiteralPreparation.program a.solve.prepareFMI3 sigs) caller callee →
        ¬ Transition.Reaches (ProgramEdge (LiteralPreparation.program a.solve.prepareFMI3 sigs)) callee caller := by
  obtain ⟨sigs, printed, covered, policy, _⟩ := actual_adapter_policy contract.adapter
  exact ⟨compiled, contract.numerical, sigs, printed, covered, policy,
    program_rank a.solve.prepareFMI3 sigs covered,
    fun _ _ first => complete_program_no_cycle a.solve.prepareFMI3 sigs covered first⟩

end Rumoca.FMI3.CallPolicy
