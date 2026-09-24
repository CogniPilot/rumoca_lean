import GALECParser.Syntax
import GALECParser.StructuralParser

/-! GALEC source entrypoint. The scanner runs once, the certified LALR parser
runs once, and structural actions consume that same CST once. Provenance is a
proof field recording the actual tokens, tree, structural value and typed-action
denotation; it never reruns parsing. This is syntax only: declarations, names,
shapes and method admission are static semantics checked after parsing. -/
namespace Rumoca.GALEC.Syntax
open _root_.Parser

def Witness (source : String) (block : AST.Block) : Prop :=
  ∃ tokens tree value,
    Scanner.Lexes scanner source.toList tokens ∧
    StructureBridge.parser.run tokens = .ok tree ∧
    StructureBridge.build tree tokens = some value ∧
    LALR.Frontend.StructuralActions.Denotes Structural.rules Token.symbol
      (.ref "block") value block

structure Parsed (source : String) where
  ast : AST.Block
  witnessed : Witness source ast

theorem witnessed_build (lexed : Scanner.lex scanner source = .ok tokens)
    (parsed : StructureBridge.parser.run tokens = .ok tree)
    (built : Structural.build tree tokens = some ast) : Witness source ast := by
  obtain ⟨value, structured, action⟩ := (Structural.build_iff tree tokens ast).mp built
  exact ⟨tokens, tree, value, (Scanner.lex_correct _ _ _).mp lexed, parsed, structured, action⟩

def parse (source : String) : Except Diagnostic (Parsed source) :=
  match lexed : Scanner.lex scanner source with
  | .error diagnostic => .error diagnostic
  | .ok tokens =>
    match parsed : StructureBridge.parser.run tokens with
    | .error _ => .error ⟨"GALEC syntax", 0, "outside the certified grammar"⟩
    | .ok tree =>
      match built : Structural.build tree tokens with
      | none => .error ⟨"GALEC action", 0, "invalid structural action result"⟩
      | some ast => .ok ⟨ast, witnessed_build lexed parsed built⟩

/-- The successful AST is exactly the token-level structural parse of the
scanner output. The right side is a specification, not a second parse. -/
theorem erase_parse (source : String) :
    (parse source).toOption.map Parsed.ast =
      (Scanner.lex scanner source).toOption.bind Structural.parse := by
  unfold parse
  split
  · rename_i diagnostic lexed
    simp [lexed, Except.toOption]
  · rename_i tokens lexed
    split
    · rename_i failure parsed
      simp [Structural.parse, lexed, parsed, Except.toOption]
    · rename_i tree parsed
      split
      · rename_i built
        simp [Structural.parse, lexed, parsed, built, Except.toOption]
      · rename_i ast built
        simp [Structural.parse, lexed, parsed, built, Except.toOption]

private theorem witness_iff (source : String) (ast : AST.Block) :
    Witness source ast ↔ (Scanner.lex scanner source).toOption.bind Structural.parse = some ast := by
  unfold Witness
  simp only [← Scanner.lex_correct]
  cases lexed : Scanner.lex scanner source with
  | error diagnostic => simp [Except.toOption]
  | ok tokens =>
    simp only [Except.toOption, Option.bind_some, Except.ok.injEq, exists_and_left,
      exists_eq_left', Structural.parse_iff]

/-- All-source success equivalence, with actual provenance rather than a
free AST or an example-specific certificate. -/
theorem success_iff (source : String) (ast : AST.Block) :
    (∃ result, parse source = .ok result ∧ result.ast = ast) ↔ Witness source ast := by
  rw [witness_iff, ← erase_parse]
  cases result : parse source <;> simp [Except.toOption]

/-- A source text has at most one witnessed tree. -/
theorem witness_unique (first : Witness source a) (second : Witness source b) : a = b := by
  obtain ⟨left, parsedLeft, sameLeft⟩ := (success_iff source a).mpr first
  obtain ⟨right, parsedRight, sameRight⟩ := (success_iff source b).mpr second
  rw [parsedLeft] at parsedRight
  cases parsedRight
  exact sameLeft.symm.trans sameRight

theorem lexical_error (failure : Scanner.lex scanner source = .error diagnostic) :
    parse source = .error diagnostic := by
  unfold parse
  split
  · rename_i other found
    have same := Except.error.inj (found.symm.trans failure)
    cases same
    rfl
  · rename_i tokens found
    rw [failure] at found
    contradiction

/-- Exact accepted language, inherited from the reusable LALR/structural
certificates for all source strings, not a collection of successful examples. -/
theorem accepts_iff (source : String) :
    (∃ result, parse source = .ok result) ↔ ∃ tokens,
      Scanner.Lexes scanner source.toList tokens ∧
      EBNF.Accepts Generated.sourceGrammar (tokens.map Token.symbol) := by
  have erased := erase_parse source
  simp only [← Scanner.lex_correct]
  constructor
  · rintro ⟨result, parsed⟩
    rw [parsed] at erased
    cases lexed : Scanner.lex scanner source with
    | error diagnostic => simp [lexed, Except.toOption] at erased
    | ok tokens =>
      simp only [lexed, Except.toOption, Option.map_some, Option.bind_some] at erased
      exact ⟨tokens, rfl, (Structural.accepts_iff tokens).mp ⟨result.ast, erased.symm⟩⟩
  · rintro ⟨tokens, lexed, accepted⟩
    obtain ⟨ast, success⟩ := (Structural.accepts_iff tokens).mpr accepted
    simp only [lexed, Except.toOption, Option.bind_some, success] at erased
    cases result : parse source with
    | error diagnostic => simp [result] at erased
    | ok value => exact ⟨value, rfl⟩

/-- A successful certified CST cannot fail the structural action stage. -/
theorem successful_tree (lexed : Scanner.lex scanner source = .ok tokens)
    (parsed : StructureBridge.parser.run tokens = .ok tree) :
    ∃ result, parse source = .ok result := by
  obtain ⟨ast, built⟩ := Structural.build_total parsed
  have erased := erase_parse source
  simp only [lexed, Except.toOption, Option.bind_some, Structural.parse, parsed, built] at erased
  cases result : parse source with
  | error diagnostic => simp [result] at erased
  | ok value => exact ⟨value, rfl⟩

end Rumoca.GALEC.Syntax
