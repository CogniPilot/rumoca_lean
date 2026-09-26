import ModelicaParser.Lexer
import ModelicaParser.StructuralParser
import ModelicaParser.ActionYield

/-! Modelica source entrypoint. The lexer runs once, the certified LALR parser
runs once, and structural actions consume that same tree once. The result
records the actual tokens and the proof that the general syntax tree is their
structural parse; it never reruns parsing. This is syntax only: which classes,
declarations and equations are admitted is static semantics after parsing. -/
namespace Rumoca.Modelica
open _root_.Parser

/-- A certified parse of one source text. -/
structure Parsed (source : String) where
  tokens : List Token
  ast : AST.StoredDefinition
  lexical : lex source = .ok tokens
  syntactic : Structural.parse tokens = some ast

def parse (source : String) : Except Diagnostic (Parsed source) :=
  match lexed : lex source with
  | .error diagnostic => .error diagnostic
  | .ok tokens =>
    match parsed : Structural.parse tokens with
    | none => .error ⟨"parse", 0, "outside the certified Modelica grammar"⟩
    | some ast => .ok ⟨tokens, ast, lexed, parsed⟩

namespace Parsed
variable {source : String}

/-- The syntax tree retains every token: printing it gives the lexed input. -/
theorem printed (p : Parsed source) : Print.storedDefinition p.ast = p.tokens :=
  Structural.parse_printed p.syntactic

theorem lexes (p : Parsed source) : Lexes source.toList p.tokens :=
  (lex_correct source _).mp p.lexical

/-- The accepted tokens are in the independent recursive EBNF language. -/
theorem in_ebnf (p : Parsed source) :
    EBNF.Accepts Generated.sourceGrammar (p.tokens.map Token.symbol) :=
  (Structural.accepts_iff p.tokens).mp ⟨p.ast, p.syntactic⟩

end Parsed

/-- A certified parse describes the actual executable parser result. -/
theorem parse_eq_parsed (p : Parsed source) : parse source = .ok p := by
  obtain ⟨tokens, ast, lexed, parsed⟩ := p
  unfold parse
  split
  · rename_i diagnostic failed
    rw [lexed] at failed
    contradiction
  · rename_i other found
    cases Except.ok.inj (found.symm.trans lexed)
    split
    · rename_i missing
      rw [parsed] at missing
      contradiction
    · rename_i result same
      cases Option.some.inj (same.symm.trans parsed)
      rfl

/-- Every source text has at most one certified parse. -/
theorem Parsed.unique (p q : Parsed source) : p = q :=
  Except.ok.inj ((parse_eq_parsed p).symm.trans (parse_eq_parsed q))

/-- Exact accepted language, inherited from the reusable LALR and structural
certificates for all source strings. -/
theorem accepts_iff (source : String) :
    (∃ result, parse source = .ok result) ↔ ∃ tokens,
      Lexes source.toList tokens ∧ EBNF.Accepts Generated.sourceGrammar (tokens.map Token.symbol) := by
  constructor
  · rintro ⟨result, _⟩
    exact ⟨result.tokens, result.lexes, result.in_ebnf⟩
  · rintro ⟨tokens, lexes, accepted⟩
    obtain ⟨ast, parsed⟩ := (Structural.accepts_iff tokens).mpr accepted
    exact ⟨_, parse_eq_parsed ⟨tokens, ast, (lex_correct source tokens).mpr lexes, parsed⟩⟩

end Rumoca.Modelica
