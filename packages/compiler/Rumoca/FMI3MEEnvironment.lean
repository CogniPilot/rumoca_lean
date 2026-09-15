import Rumoca.FMI3AdapterProofs
import RumocaFMI3.MEEnvironment

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory StaticFactory CLiteral

/-- All admitted ME control, state and derivative calls use one actual compiled
definition table and literal pool. The independent function-section printer
contract and all prepared rejection/logging contracts are retained. -/
theorem adapter_me_environment (contract : AdapterContract a adapter) :
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      MEEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool := by
  obtain ⟨sigs, unique, _, printed, _, functions, _, _, _, ready,
    _, _, _, _, states, derivative, _, _, _, _, _, _, _, time, entries, completed, discrete, _, _, _, evaluationContract, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  refine ⟨sigs, pool, made, printed, functions, ?_⟩
  exact ⟨StateEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique states.member made,
    DerivativeEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique derivative.member
      derivative.numerical.fresh made,
    MEControlEnvironment.TimeControl.prepared_correct a.solve.prepareFMI3 sigs unique time.member made,
    fun entry => MEControlEnvironment.EntryControl.prepared_correct a.solve.prepareFMI3 entry sigs
      unique (entries entry).member made,
    MEControlEnvironment.CompletedControl.prepared_correct a.solve.prepareFMI3 sigs unique completed.member made,
    MEControlEnvironment.DiscreteControl.prepared_correct a.solve.prepareFMI3 sigs unique discrete.member made,
      evaluationContract.prepared pool made⟩

end Rumoca.FMI3
end
