import RumocaFMI3.InitializationProtocolHistory
import RumocaFMI3.CSRunEnvironment
import RumocaFMI3.MEEnvironment

namespace Rumoca.FMI3.InitializationProtocol
open CTree CLiteral

/-- Creation and every later protocol segment use these contracts for one
prepared table and literal pool. The CS environment includes common lifecycle
calls, shared by both interfaces. No stage supplies a new program identity. -/
structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  getter : Float64Environment.PreparedContract model sigs pool
  setter : Float64SetEnvironment.PreparedContract model sigs pool
  counts : ∀ events, CountEnvironment.PreparedContract model sigs events pool
  nominals : NominalEnvironment.PreparedContract model sigs pool
  cs : CSRunEnvironment.PreparedContract model sigs pool
  me : MEEnvironment.PreparedContract model sigs pool

end Rumoca.FMI3.InitializationProtocol
