import Rumoca.Compiler
import RumocaCore.Initialization.Diagnostics

/-! Every compilation artifact owns checked source provenance. Initialization
notices use it directly, without attachment, a second parse, or fallback ranges. -/
namespace Rumoca

def Artifact.initializationDiagnostics (artifact : Artifact source) :
    List (Parser.Source.Diagnostic source.source) :=
  Initialization.diagnostics artifact.solve.initial artifact.parsed.ast.state
    (artifact.located.fieldSpan 3)

end Rumoca
