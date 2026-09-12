import Parser.EBNF.Syntax
import Parser.EBNF.Lexical

/-! Declarative syntax for the supported EBNF text notation. These judgments
describe complete token sequences, not a reader state, fuel or execution trace.
Grouping changes precedence; concatenation binds more tightly than alternatives.
The expression AST uses right association. Character spelling/trivia is a
separate lexical obligation. This is the documented dialect, not all ISO 14977. -/
namespace Parser.EBNF.Metalanguage

mutual
  inductive Expression : Expr → List Lexeme → Prop where
    | sequence : Sequence e tokens → Expression e tokens
    | alternative : Sequence a left → Expression b right →
        Expression (.alt a b) (left ++ .punct '|' :: right)

  inductive Sequence : Expr → List Lexeme → Prop where
    | primary : Primary e tokens → Sequence e tokens
    | comma : Primary a left → Sequence b right →
        Sequence (.seq a b) (left ++ .punct ',' :: right)
    | adjacent : Primary a left → Sequence b right →
        Sequence (.seq a b) (left ++ right)

  inductive Primary : Expr → List Lexeme → Prop where
    | identifier : Primary (.terminal .ident) [.name "IDENT"]
    | reference (ordinary : name ≠ "IDENT") : Primary (.ref name) [.name name]
    | literal : Primary (.terminal (.literal text)) [.text text]
    | group : Expression e tokens → Primary e (.punct '(' :: tokens ++ [.punct ')'])
    | optional : Expression e tokens →
        Primary (.optional e) (.punct '[' :: tokens ++ [.punct ']'])
    | many : Expression e tokens → Primary (.many e) (.punct '{' :: tokens ++ [.punct '}'])
end

theorem Primary.nonempty (h : Primary expr tokens) : tokens ≠ [] := by
  cases h <;> simp

theorem Sequence.nonempty (h : Sequence expr tokens) : tokens ≠ [] := by
  cases h with
  | primary p => exact p.nonempty
  | comma p s => simp
  | adjacent p s =>
    intro empty
    exact p.nonempty (List.append_eq_nil_iff.mp empty).1

theorem Expression.nonempty (h : Expression expr tokens) : tokens ≠ [] := by
  cases h with
  | sequence s => exact s.nonempty
  | alternative s e => simp

/-- Definitions keep source order. Name admissibility is a separate condition
so syntax does not silently incorporate the reader's duplicate-name search. -/
inductive Rules : Grammar → List Lexeme → Prop where
  | nil : Rules [] []
  | cons (separator : sep = '=' ∨ sep = ':') (body : Expression expr tokens)
      (rest : Rules grammar suffix) :
      Rules ((name, expr) :: grammar)
        (.name name :: .punct sep :: tokens ++ .punct ';' :: suffix)

def NamesValid (grammar : Grammar) : Prop :=
  (grammar.map Prod.fst).Nodup ∧ ∀ rule ∈ grammar, rule.1 ≠ "IDENT"

theorem namesValid_nil : NamesValid [] := by simp [NamesValid]

theorem namesValid_cons : NamesValid ((name, expr) :: grammar) ↔
    name ≠ "IDENT" ∧ name ∉ grammar.map Prod.fst ∧ NamesValid grammar := by
  simp [NamesValid, List.nodup_cons, and_assoc, and_left_comm, and_comm]

/-- The public reader promises at least one uniquely named rule. Undefined
references are a lowering error, rather than a token-syntax restriction. -/
def DenotesTokens (tokens : List Lexeme) (grammar : Grammar) : Prop :=
  Rules grammar tokens ∧ NamesValid grammar ∧ grammar ≠ []

/-- Complete EBNF text notation, independent of the character/token reader.
The notation specifies the supported dialect, including lexical boundaries. -/
def Denotes (source : String) (grammar : Grammar) : Prop :=
  ∃ tokens, Lexes source.toList tokens ∧ DenotesTokens tokens grammar

end Parser.EBNF.Metalanguage
