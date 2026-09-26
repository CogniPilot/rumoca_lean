import ModelicaParser.Lexer
import ModelicaParser.StructuralParser
import ModelicaParser.ActionYield

/-! Modelica source entrypoint. The lexer runs once, the certified LALR parser
runs once on the code tokens (the lexemes without comments), and structural
actions consume that same tree once. The result records the actual lexemes and
the proof that the general syntax tree is the structural parse of their code
tokens; it never reruns parsing. This is syntax only: which classes,
declarations and equations are admitted is static semantics after parsing. -/
namespace Rumoca.Modelica
open _root_.Parser

/-- A comment lexeme. -/
def isComment : Token → Bool
  | .comment _ => true
  | _ => false

/-- The lexemes the grammar reads: every lexeme except comments. -/
def code (lexemes : List Token) : List Token := lexemes.filter fun t => !isComment t

/-- Without comments, the code tokens are all lexemes. -/
theorem code_uncommented {lexemes : List Token} (uncommented : lexemes.all (fun t => !isComment t)) :
    code lexemes = lexemes := List.filter_eq_self.mpr (by simpa using uncommented)

/-- A certified parse of one source text. -/
structure Parsed (source : String) where
  lexemes : List Token
  ast : AST.StoredDefinition
  lexical : lex source = .ok lexemes
  syntactic : Structural.parse (code lexemes) = some ast

def parse (source : String) : Except Diagnostic (Parsed source) :=
  match lexed : lex source with
  | .error diagnostic => .error diagnostic
  | .ok lexemes =>
    match parsed : Structural.parse (code lexemes) with
    | none => .error ⟨"parse", 0, "outside the certified Modelica grammar"⟩
    | some ast => .ok ⟨lexemes, ast, lexed, parsed⟩

namespace Parsed
variable {source : String}

/-- The tokens the grammar parsed. -/
def tokens (p : Parsed source) : List Token := code p.lexemes

/-- The syntax tree retains every code token: printing it gives them. -/
theorem printed (p : Parsed source) : Print.storedDefinition p.ast = p.tokens :=
  Structural.parse_printed p.syntactic

theorem lexes (p : Parsed source) : Lexes source.toList p.lexemes :=
  (lex_correct source _).mp p.lexical

/-- The parsed tokens are in the independent recursive EBNF language. -/
theorem in_ebnf (p : Parsed source) :
    EBNF.Accepts Generated.sourceGrammar (p.tokens.map Token.symbol) :=
  (Structural.accepts_iff p.tokens).mp ⟨p.ast, p.syntactic⟩

end Parsed

/-- A certified parse describes the actual executable parser result. -/
theorem parse_eq_parsed (p : Parsed source) : parse source = .ok p := by
  obtain ⟨lexemes, ast, lexed, parsed⟩ := p
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
    (∃ result, parse source = .ok result) ↔ ∃ lexemes,
      Lexes source.toList lexemes ∧
        EBNF.Accepts Generated.sourceGrammar ((code lexemes).map Token.symbol) := by
  constructor
  · rintro ⟨result, _⟩
    exact ⟨result.lexemes, result.lexes, result.in_ebnf⟩
  · rintro ⟨lexemes, lexes, accepted⟩
    obtain ⟨ast, parsed⟩ := (Structural.accepts_iff (code lexemes)).mpr accepted
    exact ⟨_, parse_eq_parsed ⟨lexemes, ast, (lex_correct source lexemes).mpr lexes, parsed⟩⟩

end Rumoca.Modelica
