import RumocaFMI3.StepContract
import RumocaFMI3.ResetEnvironment
import RumocaFMI3.TerminationEnvironment
import RumocaFMI3.InitializationRuntime

noncomputable section
namespace Rumoca.FMI3.CSRunEnvironment
open CTree CMemory StaticFactory

/-- Stepping and lifecycle definitions refer to one prepared program. This
context can be reused after arbitrary proved initialization histories. -/
structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap CLiteral.functionNames)) : Prop where
  step : StepCalls.PreparedContract model sigs pool
  reset : (LiteralPreparation.program model sigs).definitions Reset.signature.name =
    some (.tree (Runtime.function model Reset.signature))
  enter : (LiteralPreparation.program model sigs).definitions InitializationCalls.signature.name =
    some (.tree InitializationCalls.function)
  exit : (LiteralPreparation.program model sigs).definitions InitializationExit.signature.name =
    some (.tree (Runtime.function model InitializationExit.signature))
  terminate : (LiteralPreparation.program model sigs).definitions Termination.signature.name =
    some (.tree (Runtime.function model Termination.signature))
  release : (LiteralPreparation.program model sigs).definitions StaticRelease.function.signature.name =
    some (.tree StaticRelease.function)

theorem PreparedContract.execution (prepared : PreparedContract model sigs pool)
    (header : CFenv.Header) (objects : Objects) (firstBlock : Nat) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model sigs →
      StaticReset.ExecutionContract program ∧
      program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) ∧
      program.internal.definitions InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) ∧
      Termination.QuietContract program ∧
      program.internal.definitions StaticRelease.function.signature.name = some (.tree StaticRelease.function) := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual
  exact ⟨ResetEnvironment.execution_correct header objects _ model program (by rw [actual]; exact prepared.reset),
    by rw [actual]; exact prepared.enter,
    by rw [actual]; exact prepared.exit,
    TerminationEnvironment.quiet_correct header objects _ model program (by rw [actual]; exact prepared.terminate),
    by rw [actual]; exact prepared.release⟩

end Rumoca.FMI3.CSRunEnvironment
end
