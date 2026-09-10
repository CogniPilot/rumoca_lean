import ModelicaParser.Array.Located
import RumocaCore.Array.Solve

/-! Development source-to-Solve preparation. The result retains the original
located parse and the certificate for the stored executable kernel. This API
does not admit the array profile to production C or FMI generation. -/
namespace Rumoca.ArrayCompiler
open ArrayProfile

structure Prepared (source : String) where
  parsed : LocatedParsed source
  resolved : parsed.parsed.ast.Resolved
  kernel : Solve.PointwiseIVP stateShape
  kernel_lowered : kernel = Solved.lower (DAE.lower (Flat.lower parsed.parsed.ast resolved))

def prepareParsed (parsed : LocatedParsed source) (resolved : parsed.parsed.ast.Resolved) :
    Prepared source :=
  ⟨parsed, resolved, Solved.lower (DAE.lower (Flat.lower parsed.parsed.ast resolved)), rfl⟩

def prepare (source : String) : Except (_root_.Parser.Source.Diagnostic source) (Prepared source) := do
  let parsed ← parseLocated source
  let resolved ← ArrayProfile.LocatedParsed.resolve parsed
  return prepareParsed parsed resolved.down

end Rumoca.ArrayCompiler
