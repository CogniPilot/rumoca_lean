import Rumoca.Compiler
import RumocaEFMI.AlgorithmCode
import RumocaEFMI.StartupMap

namespace Rumoca

/-- Select the checked DAE product. GALEC is not reconstructed from the
numerical Solve instructions, and does not change that numerical path. -/
def Artifact.algorithmCode (a : Artifact source) : GALEC.Model a.parsed.ast :=
  GALEC.lower a.solve.dae

def Artifact.algorithmSource (a : Artifact source) : String :=
  EFMI.renderAlgorithm a.algorithmCode

def Artifact.algorithmSolve (a : Artifact source) : Solve.Algorithm.Model a.parsed.ast :=
  Solve.Algorithm.prepare a.algorithmCode

def Artifact.productionSource (a : Artifact source) : Except String String :=
  (fun emission => emission.document.render) <$> EFMI.Production.StartupMap.emit a.algorithmSolve

end Rumoca
