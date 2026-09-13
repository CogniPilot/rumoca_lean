import Rumoca.FMI3BuildProofs
import RumocaFMI3.LiteralEvents

/-! The actual adapter, compiled Solve model and prepared literal pass share
one function table. The pass preserves and reflects observable C behaviors;
header/ABI interpretation and later machine compilation remain separate. -/
noncomputable section
namespace Rumoca.FMI3
open CTree CLiteral

theorem literal_events_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      LiteralPreparation.EventPreparedContract a.solve.prepareFMI3 sigs pool := by
  obtain ⟨sigs, _, _, printed, _, grammar, _, _, _, ready, _, _, events, _⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  exact ⟨compiled, sigs, pool, printed, grammar, made, events pool made⟩

end Rumoca.FMI3
