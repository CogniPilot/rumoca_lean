import ModelicaParser.Array.Located
import ModelicaParser.ActionsLocatedTotal
import RumocaCore.Array.Solve

/-! Development source-to-Solve preparation. The result retains the original
located parse and the certificate for the stored executable kernel. This API
does not admit the array profile to production C or FMI generation. -/
namespace Rumoca.ArrayCompiler
open ArrayProfile

structure Prepared (source : String) where
  parsed : ArrayProfile.LocatedParsed source
  resolved : parsed.parsed.ast.Resolved
  kernel : Solve.PointwiseIVP stateShape
  kernel_lowered : kernel = Solved.lower (DAE.lower (Flat.lower parsed.parsed.ast resolved))

def prepareParsed (parsed : ArrayProfile.LocatedParsed source)
    (resolved : parsed.parsed.ast.Resolved) : Prepared source :=
  ⟨parsed, resolved, Solved.lower (DAE.lower (Flat.lower parsed.parsed.ast resolved)), rfl⟩

def prepare (source : String) : Except (_root_.Parser.Source.Diagnostic source) (Prepared source) := do
  let parsed ← ArrayProfile.parseLocated source
  let resolved ← ArrayProfile.LocatedParsed.resolve parsed
  return prepareParsed parsed resolved.down

/-- The total located frontend implements the same successful parse and
resolution for a pinned array AST. As in the unit profile's `compile_eq_parsed`,
this identifies `prepare` with the actual attachment computation for an already
certified parse, without kernel-evaluating the LR parser on the source text. -/
theorem prepare_eq_parsed (parsed : ArrayProfile.Parsed source)
    (resolved : parsed.ast.Resolved) :
    prepare source = .ok (prepareParsed parsed.located resolved) := by
  simp only [prepare, ArrayProfile.parseLocated, bind, Except.bind, parsed.parseLocated_eq]
  rw [ArrayProfile.LocatedParsed.resolve_complete parsed.located resolved]
  rfl

end Rumoca.ArrayCompiler
