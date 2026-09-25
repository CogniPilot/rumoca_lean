import Rumoca.Compiler
import RumocaEFMI.AlgorithmCode
import RumocaEFMI.StartupMap

namespace Rumoca

/-- Prepare the Algorithm Code root from the checked DAE product. It is not
reconstructed from the numerical Solve instructions, and does not change that
numerical path. -/
def Artifact.algorithmSolve (a : Artifact source) : Solve.Algorithm.Model a.parsed.ast :=
  Solve.Algorithm.prepare a.solve.dae

def Artifact.algorithmSource (a : Artifact source) : String :=
  EFMI.renderAlgorithm a.algorithmSolve

def Artifact.productionSource (a : Artifact source) : Except String String :=
  (fun emission => emission.document.render) <$> EFMI.Production.StartupMap.emit a.algorithmSolve

end Rumoca
