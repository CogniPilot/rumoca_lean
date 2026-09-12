import Parser.EBNF.Syntax

/-! Character-level notation for the supported EBNF dialect. The relations
refer to source characters and token values, without calling the lexer.
Comments are non-nested; quoted text has no escapes; names use maximal munch. -/
namespace Parser.EBNF.Metalanguage

def QuotedBody (delimiter : Char) (body : List Char) : Prop :=
  ∀ char ∈ body, char ≠ delimiter ∧ char ≠ '\\'

def CommentBody (body : List Char) : Prop :=
  ¬ List.IsInfix ['*', ')'] body

theorem commentBody_nil : CommentBody [] := by simp [CommentBody]

theorem commentBody_cons : CommentBody (char :: body) ↔
    CommentBody body ∧ (char = '*' → body.head? ≠ some ')') := by
  constructor
  · intro valid
    refine ⟨fun hit => valid (List.infix_cons hit), ?_⟩
    intro equal head
    subst char
    cases body with
    | nil => simp at head
    | cons next tail =>
      have : next = ')' := by simpa using head
      subst next
      exact valid ⟨[], tail, rfl⟩
  · rintro ⟨tailValid, firstValid⟩ ⟨before, after, equal⟩
    cases before with
    | nil =>
      have parts := List.cons.inj equal
      exact firstValid parts.1.symm (by rw [← parts.2]; rfl)
    | cons first before =>
      have parts := List.cons.inj equal
      exact tailValid ⟨before, after, parts.2⟩

def NameBody (first : Char) (tail rest : List Char) : Prop :=
  identStart first = true ∧ (∀ char ∈ tail, identRest char = true) ∧
    (∀ char, rest.head? = some char → identRest char = false)

inductive Lexes : List Char → List Lexeme → Prop where
  | nil : Lexes [] []
  | space (white : asciiSpace char = true) (rest : Lexes chars tokens) :
      Lexes (char :: chars) tokens
  | block (bodyValid : CommentBody body) (rest : Lexes chars tokens) :
      Lexes ('(' :: '*' :: (body ++ '*' :: ')' :: chars)) tokens
  | line (bodyValid : '\n' ∉ body) (boundary : chars = [] ∨ chars.head? = some '\n')
      (rest : Lexes chars tokens) : Lexes ('/' :: '/' :: (body ++ chars)) tokens
  | quoted (quote : delimiter = '"' ∨ delimiter = '\'')
      (bodyValid : QuotedBody delimiter body) (rest : Lexes chars tokens) :
      Lexes (delimiter :: (body ++ delimiter :: chars)) (.text (String.ofList body) :: tokens)
  | name (bodyValid : NameBody first tail chars) (rest : Lexes chars tokens) :
      Lexes (first :: (tail ++ chars)) (.name (String.ofList (first :: tail)) :: tokens)
  | punctuation (symbol : char ∈ ['=', ':', ';', ',', '|', '(', ')', '[', ']', '{', '}'])
      (boundary : char = '(' → chars.head? ≠ some '*') (rest : Lexes chars tokens) :
      Lexes (char :: chars) (.punct char :: tokens)

end Parser.EBNF.Metalanguage
