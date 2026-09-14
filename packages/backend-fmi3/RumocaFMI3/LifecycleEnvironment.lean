import RumocaFMI3.ResetEnvironment
import RumocaFMI3.TerminationEnvironment
import RumocaFMI3.InitializationRuntime

noncomputable section
namespace Rumoca.FMI3.LifecycleEnvironment
open CTree CMemory StaticFactory

/-- Shared reset, initialization, termination and release definitions refer to
one prepared program, independently of ME or CS numerical operations. -/
structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature) : Prop where
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

theorem PreparedContract.execution (prepared : PreparedContract model sigs)
    (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model sigs →
      StaticReset.ExecutionContract program ∧
      program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) ∧
      program.internal.definitions InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) ∧
      Termination.QuietContract program ∧
      program.internal.definitions StaticRelease.function.signature.name = some (.tree StaticRelease.function) := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program actual
  exact ⟨ResetEnvironment.execution_correct header objects _ model program (by rw [actual]; exact prepared.reset),
    by rw [actual]; exact prepared.enter,
    by rw [actual]; exact prepared.exit,
    TerminationEnvironment.quiet_correct header objects _ model program (by rw [actual]; exact prepared.terminate),
    by rw [actual]; exact prepared.release⟩

end Rumoca.FMI3.LifecycleEnvironment
end
