import Rumoca.Compiler
import Rumoca.ConstantProduction
import RumocaCore.Initialization.Diagnostics

/-! Every compilation artifact owns checked source provenance. Initialization
notices use it directly, without attachment, a second parse, or fallback ranges. -/
namespace Rumoca

def Artifact.initializationDiagnostics (artifact : Artifact source) :
    List (Parser.Source.Diagnostic source.source) :=
  Initialization.diagnostics artifact.solve.initial artifact.parsed.ast.state
    (artifact.located.fieldSpan 3)

/-- The §8.6 notices of the constant-rate completion: for each declared state, in
source order, the notices of its completed plan at the state's identifier in its
`Real ident ;` declaration (token `3 + 3 i` after `model name`). -/
def ConstantArtifact.initializationDiagnostics (a : ConstantArtifact input) :
    List (Parser.Source.Diagnostic input.source) :=
  a.prepared.parsed.parsed.ast.states.zipIdx.flatMap fun (state, i) =>
    Initialization.diagnostics (a.prepared.parsed.parsed.ast.plan state) state
      (a.prepared.parsed.tokenSpan (3 + 3 * i))

end Rumoca
