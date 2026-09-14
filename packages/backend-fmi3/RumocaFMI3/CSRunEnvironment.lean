import RumocaFMI3.StepContract
import RumocaFMI3.LifecycleEnvironment

noncomputable section
namespace Rumoca.FMI3.CSRunEnvironment
open CTree CMemory StaticFactory

/-- CS numerical and common lifecycle contracts share one prepared program. -/
structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap CLiteral.functionNames)) : Prop
    extends LifecycleEnvironment.PreparedContract model sigs where
  step : StepCalls.PreparedContract model sigs pool

theorem PreparedContract.execution (prepared : PreparedContract model sigs pool)
    (header : CFenv.Header) (objects : Objects) (firstBlock : Nat) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model sigs →
      StaticReset.ExecutionContract program ∧
      program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) ∧
      program.internal.definitions InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) ∧
      Termination.QuietContract program ∧
      program.internal.definitions StaticRelease.function.signature.name = some (.tree StaticRelease.function) :=
  prepared.toPreparedContract.execution header objects (pool.addresses firstBlock)

end Rumoca.FMI3.CSRunEnvironment
end
