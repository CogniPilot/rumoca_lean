import ModelicaParser.Actions
import ModelicaParser.Array.Syntax

open _root_.Parser

namespace Rumoca.ArrayProfile

/-- A linear identifier pass proposes the structured AST. Checking its entire
token sequence rejects extra tokens, changed extents and malformed operators.
The generic EBNF recognizer remains a separate required check. -/
private def candidate (ids : List String) : Option Model :=
  match ids with
    | [name, input, state, startAttr, fixedAttr, derivative, rhs, endName] =>
      some ⟨⟨name, input, state, startAttr, fixedAttr⟩, .driven derivative rhs, endName⟩
    | [name, input, state, startAttr, fixedAttr, output, derivative, left, right,
        assigned, callee, argLeft, argRight, wrt, endName] =>
      some ⟨⟨name, input, state, startAttr, fixedAttr⟩,
        .jacobian output derivative ⟨left, right⟩ assigned ⟨callee, ⟨argLeft, argRight⟩, wrt⟩,
        endName⟩
    | _ => none

def decode (ts : List Token) : Option Model :=
  match candidate (ts.filterMap fun t => match t with | .ident n => some n | .literal _ => none) with
  | none => none
  | some model => if ts = model.tokens then some model else none

theorem decode_sound (ts : List Token) (m : Model) (h : decode ts = some m) :
    ts = m.tokens := by
  unfold decode at h
  split at h
  · contradiction
  · split at h
    · cases Option.some.inj h; assumption
    · contradiction

theorem decode_complete (m : Model) : decode m.tokens = some m := by
  cases m with
  | mk header body endName =>
    cases body <;> simp [decode, candidate, Model.tokens, Header.tokens, Body.tokens, Product.tokens, Call.tokens]

private def drivenPattern : List RuntimeGenerated.Letter :=
  (Model.mk ⟨"", "", "", "", ""⟩ (.driven "" "") "").tokens.map
    (RuntimeGenerated.encode ∘ Token.symbol)

private def jacobianPattern : List RuntimeGenerated.Letter :=
  (Model.mk ⟨"", "", "", "", ""⟩ (.jacobian "" "" ⟨"", ""⟩ "" ⟨"", ⟨"", ""⟩, ""⟩) "").tokens.map
    (RuntimeGenerated.encode ∘ Token.symbol)

set_option maxRecDepth 10000 in
theorem recognized (m : Model) :
    RuntimeGenerated.recognize (m.tokens.map (RuntimeGenerated.encode ∘ Token.symbol)) = true := by
  cases m with
  | mk header body endName =>
    cases body with
    | driven =>
      change RuntimeGenerated.recognize drivenPattern = true
      decide +kernel
    | jacobian =>
      change RuntimeGenerated.recognize jacobianPattern = true
      decide +kernel

def actions : ParserActions.Actions Model :=
  ⟨Model.tokens, decode, decode_sound, decode_complete, recognized⟩

abbrev Parsed := ParserActions.Parsed actions
def parse := ParserActions.parse actions

end Rumoca.ArrayProfile
