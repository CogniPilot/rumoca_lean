import ModelicaParser.Array.Parser
import ModelicaParser.ActionsLocated

namespace Rumoca.ArrayProfile

open _root_.Parser

abbrev LocatedParsed := ParserActions.LocatedParsed actions
def parseLocated := ParserActions.parseLocated actions

/-- A call's spelling is certified at each operand's actual position. Keeping
the complete aligned token stream also preserves punctuation and dimensions. -/
structure LocatedCall (source : String) (call : Call) where
  name : Source.Span source
  left : Source.Span source
  right : Source.Span source
  wrt : Source.Span source
  closing : Source.Span source
  name_text : name.text = call.name
  left_text : left.text = call.expression.left
  right_text : right.text = call.expression.right
  wrt_text : wrt.text = call.wrt
  closing_text : closing.text = ")"

def LocatedCall.expressionSpan (c : LocatedCall source call) : Source.Span source :=
  c.left.cover c.right

def LocatedCall.span (c : LocatedCall source call) : Source.Span source :=
  ((c.name.cover c.expressionSpan).cover c.wrt).cover c.closing

theorem LocatedCall.arguments_contained (c : LocatedCall source call) :
    c.span.Contains c.expressionSpan ∧ c.span.Contains c.wrt := by
  have h₁ := (c.name.cover c.expressionSpan).cover_right c.wrt
  have h₂ := ((c.name.cover c.expressionSpan).cover c.wrt).cover_left c.closing
  have h₃ := (c.name.cover c.expressionSpan).cover_left c.wrt
  have h₄ := c.name.cover_right c.expressionSpan
  exact ⟨⟨Nat.le_trans h₂.1 (Nat.le_trans h₃.1 h₄.1),
      Nat.le_trans h₄.2 (Nat.le_trans h₃.2 h₂.2)⟩,
    ⟨Nat.le_trans h₂.1 h₁.1, Nat.le_trans h₁.2 h₂.2⟩⟩

private theorem field_text (p : LocatedParsed source)
    (h : p.parsed.ast.body = .jacobian output derivative rhs assigned call)
    (index : Nat) (token : Token)
    (ht : (p.parsed.ast.header.tokens ++
      (Body.jacobian output derivative rhs assigned call).tokens ++
      [.literal "end", .ident p.parsed.ast.endName, .literal ";"])[index]? = some token) :
    (p.tokenSpan index).text = token.text := by
  apply p.tokenSpan_text index token
  rw [ParserActions.parseTokens_sound actions p.parsed.syntactic]
  simpa only [actions, Model.tokens, h] using ht

def LocatedParsed.callLocation (p : LocatedParsed source)
    (h : p.parsed.ast.body = .jacobian output derivative rhs assigned call) :
    LocatedCall source call where
  name := p.tokenSpan 48
  left := p.tokenSpan 50
  right := p.tokenSpan 52
  wrt := p.tokenSpan 54
  closing := p.tokenSpan 55
  name_text := field_text p h 48 (.ident call.name) (by rfl)
  left_text := field_text p h 50 (.ident call.expression.left) (by rfl)
  right_text := field_text p h 52 (.ident call.expression.right) (by rfl)
  wrt_text := field_text p h 54 (.ident call.wrt) (by rfl)
  closing_text := field_text p h 55 (.literal ")") (by rfl)

def LocatedParsed.call? (p : LocatedParsed source) : Option ((c : Call) × LocatedCall source c) :=
  match h : p.parsed.ast.body with
  | .driven .. => none
  | .jacobian _ _ _ _ call => some ⟨call, p.callLocation h⟩

/-- Resolution failures keep structured ranges and the unresolved AST. -/
def LocatedParsed.resolve (p : LocatedParsed source) :
    Except (Source.Diagnostic source) (PLift p.parsed.ast.Resolved) :=
  if h : p.parsed.ast.Resolved then .ok ⟨h⟩
  else
    let m := p.parsed.ast
    let (index, message) :=
      if m.endName ≠ m.header.name then
        (match m.body with | .driven .. => 36 | .jacobian .. => 58,
         "end name does not match the model name")
      else if m.header.startAttribute ≠ "start" then (17, "expected each start=0")
      else if m.header.fixedAttribute ≠ "fixed" then (22, "expected each fixed=true")
      else match m.body with
      | .driven derivative _ =>
        if m.header.input = m.header.state then (11, "input and state names must be distinct")
        else if derivative ≠ m.header.state then (30, "derivative must reference the state")
        else (33, "right-hand side must reference the input")
      | .jacobian output derivative rhs assigned call =>
        if m.header.input = m.header.state then (11, "input and state names must be distinct")
        else if output = m.header.input ∨ output = m.header.state then (29, "Jacobian output must have a distinct name")
        else if derivative ≠ m.header.state then (39, "derivative must reference the state")
        else if rhs.left ≠ m.header.input then (42, "product operand must reference the input")
        else if rhs.right ≠ m.header.input then (44, "product operand must reference the input")
        else if assigned ≠ output then (46, "equation must assign the Jacobian output")
        else if call.builtin? ≠ some .jacobian then (48, "expected the jacobian built-in")
        else if call.expression.left ≠ m.header.input then (50, "product operand must reference the input")
        else if call.expression.right ≠ m.header.input then (52, "product operand must reference the input")
        else (54, "differentiate with respect to the input")
    .error ⟨"resolve", p.tokenSpan index, message, []⟩

theorem LocatedParsed.resolve_complete (p : LocatedParsed source) (h : p.parsed.ast.Resolved) :
    p.resolve = .ok ⟨h⟩ := by simp [resolve, h]

end Rumoca.ArrayProfile
