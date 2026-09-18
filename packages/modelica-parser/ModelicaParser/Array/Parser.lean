import ModelicaParser.Actions
import ModelicaParser.Grammar
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
  match candidate (ts.filterMap fun t => match t with | .ident n => some n | _ => none) with
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

theorem in_grammar (m : Model) :
    EBNF.Accepts Generated.sourceGrammar (m.tokens.map Token.symbol) := by
  have layout : m.tokens.map Token.symbol =
      [.literal "model", .ident] ++
        ((m.tokens.drop 2).take (m.tokens.length - 5) |>.map Token.symbol) ++
          [.literal "end", .ident, .literal ";"] := by
    cases m with
    | mk header body endName => cases body <;> rfl
  rw [layout]
  apply Grammar.accepts_composition
  cases m with
  | mk header body endName =>
    cases body <;>
      simp [Generated.rule_composition, Generated.rule_array_composition,
        Generated.rule_input, Generated.rule_output, Generated.rule_array_component_clause,
        Generated.rule_type_specifier, Generated.rule_array_subscripts, Generated.rule_subscript,
        Generated.rule_initialized_array_clause, Generated.rule_each,
        Generated.rule_zero_modification, Generated.rule_fixed_modification,
        Generated.rule_true, Generated.rule_array_body, Generated.rule_driven_equation_section,
        Generated.rule_driven_equation, Generated.rule_jacobian_body,
        Generated.rule_term, Generated.rule_factor, Generated.rule_mul_operator,
        Generated.rule_function_call_args, Generated.rule_function_arguments,
        Generated.rule_component_reference, Generated.rule_equation,
        Generated.rule_der, Generated.rule_ident,
        EBNF.Derives.seq_iff, EBNF.Derives.alt_iff, EBNF.Derives.terminal_iff,
        Model.tokens, Header.tokens, Body.tokens, Product.tokens, Call.tokens, Token.symbol]

def actions : ParserActions.Actions Model :=
  ⟨Model.tokens, decode, decode_sound, decode_complete, in_grammar⟩

abbrev Parsed := ParserActions.Parsed actions
def parse := ParserActions.parse actions

end Rumoca.ArrayProfile
