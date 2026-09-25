import RumocaFMI3.InstanceQuery
import RumocaFMI3.Float64Environment
import RumocaFMI3.Float64SetEnvironment
import RumocaFMI3.AbsentVariableContract

/-! The prepared function table and literal pool supply every instance-query
contract on later heaps, with the termination contract of the same program. -/
noncomputable section
namespace Rumoca.FMI3.InstanceQuery
open CTree CLiteral StaticFactory

structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  getter : Float64Environment.PreparedContract model sigs pool
  setter : Float64SetEnvironment.PreparedContract model sigs pool
  absent : ∀ ty write, AbsentVariables.PreparedContract model sigs ty write pool

theorem PreparedContract.quiet (prepared : PreparedContract model sigs pool)
    (header : CFenv.Header) (objects : Objects) (firstBlock : Nat) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E), program.internal = LiteralPreparation.program model sigs →
      Termination.QuietContract program → QuietContract model program := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual termination
  exact ⟨prepared.getter.quiet header E objects firstBlock program actual,
    prepared.setter.quiet header E objects firstBlock program actual,
    fun ty write => (prepared.absent ty write).quiet header E objects firstBlock program actual, termination⟩

end Rumoca.FMI3.InstanceQuery
end
