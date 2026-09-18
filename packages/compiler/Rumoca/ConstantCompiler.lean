import ModelicaParser.Constant.Located
import ModelicaParser.ActionsLocatedTotal
import RumocaCore.Constant.Semantics

/-! Development source-to-IVP preparation for the G01 constant-rate profile.
The result retains the located parse and the multi-state IVP it lowers to. This
API does not admit the profile to production C or FMI generation; the default
compiler still rejects it. -/
namespace Rumoca.ConstantCompiler
open ConstantProfile _root_.Parser

structure Prepared (source : String) where
  parsed : ConstantProfile.LocatedParsed source
  resolved : parsed.parsed.ast.Resolved
  ivp : ConstantProfile.ConstantIVP parsed.parsed.ast.states.length
  ivp_lowered : ivp = parsed.parsed.ast.lower

def prepareParsed (parsed : ConstantProfile.LocatedParsed source)
    (resolved : parsed.parsed.ast.Resolved) : Prepared source :=
  ⟨parsed, resolved, parsed.parsed.ast.lower, rfl⟩

def prepare (source : String) :
    Except (Source.Diagnostic source) (Prepared source) := do
  let parsed ← ConstantProfile.parseLocated source
  let resolved ← ConstantProfile.LocatedParsed.resolve parsed
  return prepareParsed parsed resolved.down

/-- The total located frontend implements the same successful parse and
resolution for a pinned AST, as in the array profile's `prepare_eq_parsed`. -/
theorem prepare_eq_parsed (parsed : ConstantProfile.Parsed source)
    (resolved : parsed.ast.Resolved) :
    prepare source = .ok (prepareParsed parsed.located resolved) := by
  simp only [prepare, ConstantProfile.parseLocated, bind, Except.bind, parsed.parseLocated_eq]
  rw [ConstantProfile.LocatedParsed.resolve_complete parsed.located resolved]
  rfl

end Rumoca.ConstantCompiler
