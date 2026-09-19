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

/-- Lexical notation composes across a boundary that begins with a newline. The
newline is a top-level separator: it closes any pending line comment and cannot
extend an identifier, so tokenizing a prefix and a newline-led suffix agrees
with tokenizing their concatenation. This lets a long source be certified one
bounded block at a time and joined, rather than in a single decision term. -/
theorem Lexes.append {a ta b tb : List _} (ha : Lexes a ta) (hb : Lexes b tb)
    (safe : b.head? = some '\n' ∨ b = []) : Lexes (a ++ b) (ta ++ tb) := by
  induction ha with
  | nil => simpa using hb
  | space white _ ih => exact Lexes.space white ih
  | block bodyValid _ ih =>
      simp only [List.cons_append, List.append_assoc, List.cons_append]
      exact Lexes.block bodyValid ih
  | @line body chars tokens bodyValid boundary _ ih =>
      have boundary' : chars ++ b = [] ∨ (chars ++ b).head? = some '\n' := by
        cases chars with
        | nil =>
            rcases safe with s | s
            · exact Or.inr (by simpa using s)
            · exact Or.inl (by simp [s])
        | cons x xs =>
            exact Or.inr (by
              rcases boundary with h | h
              · simp at h
              · simpa using h)
      simp only [List.cons_append, List.append_assoc]
      exact Lexes.line bodyValid boundary' ih
  | quoted quote bodyValid _ ih =>
      simp only [List.cons_append, List.append_assoc, List.cons_append]
      exact Lexes.quoted quote bodyValid ih
  | @name first tail chars tokens bodyValid _ ih =>
      have hbody : NameBody first tail (chars ++ b) := by
        refine ⟨bodyValid.1, bodyValid.2.1, ?_⟩
        intro c hc
        cases chars with
        | nil =>
            rw [List.nil_append] at hc
            rcases safe with s | s
            · have : c = '\n' := Option.some.inj (hc.symm.trans s)
              subst c; decide
            · rw [s] at hc; simp at hc
        | cons x xs =>
            rw [List.cons_append] at hc
            have : c = x := Option.some.inj hc.symm
            subst c
            exact bodyValid.2.2 x (by simp)
      simp only [List.cons_append, List.append_assoc, List.cons_append]
      exact Lexes.name hbody ih
  | @punctuation char chars tokens symbol boundary _ ih =>
      have boundary' : char = '(' → (chars ++ b).head? ≠ some '*' := by
        intro isParen
        cases chars with
        | nil =>
            rw [List.nil_append]
            rcases safe with s | s
            · rw [s]; decide
            · rw [s]; decide
        | cons x xs =>
            rw [List.cons_append]
            simpa using boundary isParen
      simp only [List.cons_append]
      exact Lexes.punctuation symbol boundary' ih

end Parser.EBNF.Metalanguage
