import ModelicaParser.Constant.Parser
import ModelicaParser.Constant.Decimal
import ModelicaParser.ActionsLocated
import ModelicaParser.ActionsLocatedTotal

/-! Located parse and name resolution for the constant-rate profile. Resolution
rejects a mismatched end name, duplicate state declarations, an equation set
that is not a permutation of the declared states (an unbound or uncovered
state), and any right-hand side that is not a signed decimal literal. The
permutation condition is what makes the equation order immaterial. -/
namespace Rumoca.ConstantProfile
open _root_.Parser

abbrev LocatedParsed := ParserActions.LocatedParsed actions
def parseLocated := ParserActions.parseLocated actions

/-- A resolved constant-rate model. The permutation of derivative names against
declared states binds every equation to a distinct declared state and covers
every state exactly once, independently of the written order. -/
def Model.Resolved (m : Model) : Prop :=
  m.endName = m.name ∧
  m.states.Nodup ∧
  (m.equations.map Equation.derivative).Perm m.states ∧
  ∀ e ∈ m.equations, (parseDecimal e.rate).isSome

instance (m : Model) : Decidable m.Resolved := by
  unfold Model.Resolved; infer_instance

/-- Resolution failures keep a structured range and a specific message. -/
def LocatedParsed.resolve (p : LocatedParsed source) :
    Except (Source.Diagnostic source) (PLift p.parsed.ast.Resolved) :=
  if h : p.parsed.ast.Resolved then .ok ⟨h⟩
  else
    let m := p.parsed.ast
    let message :=
      if m.endName ≠ m.name then "end name does not match the model name"
      else if ¬ m.states.Nodup then "duplicate state declaration"
      else if ¬ (m.equations.map Equation.derivative).Perm m.states then
        "each declared state must have exactly one der equation"
      else "right-hand side is not a signed decimal literal"
    .error ⟨"resolve", p.tokenSpan 1, message, []⟩

theorem LocatedParsed.resolve_complete (p : LocatedParsed source) (h : p.parsed.ast.Resolved) :
    p.resolve = .ok ⟨h⟩ := by simp [resolve, h]

end Rumoca.ConstantProfile
