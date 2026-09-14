import RumocaFMI3.MEControlPrepared
import RumocaFMI3.StateEnvironment
import RumocaFMI3.DerivativeEnvironment
import RumocaFMI3.MEHistory

noncomputable section
namespace Rumoca.FMI3.MEEnvironment
open CTree CMemory StaticFactory CLiteral

/-- The control and numerical contracts share one literal pool and definition
table. Each prepared contract retains its full failure and callback cases. -/
structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  states : StateEnvironment.PreparedContract model sigs pool
  derivatives : DerivativeEnvironment.PreparedContract model sigs pool
  time : MEControlEnvironment.TimeControl.PreparedContract model sigs pool
  entry : ∀ entry, MEControlEnvironment.EntryControl.PreparedContract model entry sigs pool
  completed : MEControlEnvironment.CompletedControl.PreparedContract model sigs pool
  discrete : MEControlEnvironment.DiscreteControl.PreparedContract model sigs pool

/-- Complete successful and null calls, reusable on every later valid heap.
Failure contracts remain in `PreparedContract` for eventful histories. -/
structure Quiet (model : Solve.FMI3Model source) [CInterface]
    (program : CCalls.Events.Program E) : Prop where
  control : MEHistory.Quiet program
  states : ∀ heap, StateCalls.QuietExecutionContract program heap
  derivatives : ∀ heap, DerivativeCalls.QuietExecutionContract model program heap

theorem PreparedContract.quiet (contract : PreparedContract model sigs pool)
    (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model sigs → Quiet model program := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual
  exact ⟨⟨contract.time.quiet header E objects firstBlock program actual,
      fun entry => (contract.entry entry).quiet header E objects firstBlock program actual,
      contract.completed.quiet header E objects firstBlock program actual,
      contract.discrete.quiet header E objects firstBlock program actual⟩,
    contract.states.quiet header E objects firstBlock program actual,
    contract.derivatives.quiet header E objects firstBlock program actual⟩

end Rumoca.FMI3.MEEnvironment
end
