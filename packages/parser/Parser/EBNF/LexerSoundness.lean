import Parser.EBNF.LexerCompleteness

/-! Successful character tokenization satisfies independent lexical syntax.
Together with completeness this covers the actual public lexer and its budget. -/
namespace Parser.EBNF.Reader
open Metalanguage

private theorem bind_ok {m : Except ε α} {k : α → Except ε β} {value : β}
    (result : (m >>= k) = .ok value) : ∃ x, m = .ok x ∧ k x = .ok value := by
  cases m with
  | error error => cases result
  | ok x => exact ⟨x, rfl, result⟩

private theorem drop_takeWhile_length (input : List α) (p : α → Bool) :
    input.drop (input.takeWhile p).length = input.dropWhile p := by
  have equal := congrArg (fun word => word.drop (input.takeWhile p).length)
    (List.takeWhile_append_dropWhile (p := p) (l := input))
  dsimp only at equal
  rw [List.drop_left] at equal
  exact equal.symm

private theorem dropWhile_boundary (input : List α) (p : α → Bool)
    (head : (input.dropWhile p).head? = some value) : p value = false := by
  have stop := List.head?_dropWhile_not p input
  simpa [head] using stop

private theorem line_boundary (input : List Char) :
    input.dropWhile (· != '\n') = [] ∨
      (input.dropWhile (· != '\n')).head? = some '\n' := by
  cases result : input.dropWhile (· != '\n') with
  | nil => exact .inl rfl
  | cons char tail =>
    have head : (input.dropWhile (· != '\n')).head? = some char := by simp [result]
    have stop := dropWhile_boundary input (· != '\n') head
    have equal : char = '\n' := by simpa using stop
    exact .inr (by simp [equal])

theorem tokenize_sound (parsed : tokenize fuel input = .ok tokens) : Lexes input tokens := by
  induction fuel generalizing input tokens with
  | zero => simp [tokenize] at parsed
  | succ fuel ih =>
    cases input with
    | nil =>
      have same : [] = tokens := Except.ok.inj parsed
      subst tokens
      exact .nil
    | cons char chars =>
      unfold tokenize at parsed
      split at parsed
      · rename_i white
        exact .space white (ih parsed)
      · split at parsed
        · rename_i block
          have opener : (char :: chars).take 2 = ['(', '*'] := by simpa using block
          cases chars with
          | nil => simp at opener
          | cons next chars =>
            have parts : char = '(' ∧ next = '*' := by simpa using opener
            obtain ⟨rfl, rfl⟩ := parts
            obtain ⟨following, commentRead, tokenRead⟩ := bind_ok parsed
            obtain ⟨body, sourceEq, bodyValid⟩ := comment_sound commentRead
            have valid := Lexes.block bodyValid (ih tokenRead)
            dsimp only [List.drop] at sourceEq
            simpa only [sourceEq] using valid
        · rename_i notBlock
          split at parsed
          · rename_i line
            have opener : (char :: chars).take 2 = ['/', '/'] := by simpa using line
            cases chars with
            | nil => simp at opener
            | cons next chars =>
              have parts : char = '/' ∧ next = '/' := by simpa using opener
              obtain ⟨rfl, rfl⟩ := parts
              have inside : '\n' ∉ chars.takeWhile (· != '\n') := by
                intro member
                have property := List.all_eq_true.mp (List.all_takeWhile (p := (· != '\n')) (l := chars)) '\n' member
                simp at property
              have valid := Lexes.line inside (line_boundary chars) (ih parsed)
              simpa only [List.takeWhile_append_dropWhile] using valid
          · split at parsed
            · rename_i quote
              have delimiter : char = '"' ∨ char = '\'' := by simpa using quote
              obtain ⟨⟨text, following⟩, quotedRead, finish⟩ := bind_ok parsed
              obtain ⟨remaining, tokenRead, finish⟩ := bind_ok finish
              have same := Except.ok.inj finish
              subst tokens
              obtain ⟨body, charsEq, textEq, bodyValid⟩ := quoted_sound quotedRead
              have valid := Lexes.quoted delimiter bodyValid (ih tokenRead)
              simpa only [← charsEq, ← textEq] using valid
            · split at parsed
              · rename_i starts
                have firstRest : identRest char = true := by simp [identRest, starts]
                dsimp only at parsed
                simp only [List.takeWhile_cons_of_pos firstRest, List.length_cons,
                  List.drop_succ_cons] at parsed
                rw [drop_takeWhile_length] at parsed
                obtain ⟨remaining, tokenRead, finish⟩ := bind_ok parsed
                have same := Except.ok.inj finish
                subst tokens
                have bodyValid : NameBody char (chars.takeWhile identRest) (chars.dropWhile identRest) := by
                  refine ⟨starts, List.all_eq_true.mp List.all_takeWhile, ?_⟩
                  intro value head
                  exact dropWhile_boundary chars identRest head
                have valid := Lexes.name bodyValid (ih tokenRead)
                simpa only [List.takeWhile_append_dropWhile] using valid
              · split at parsed
                · rename_i punct
                  have symbol : char ∈ ['=', ':', ';', ',', '|', '(', ')', '[', ']', '{', '}'] := by
                    simpa using punct
                  have boundary : char = '(' → chars.head? ≠ some '*' := by
                    intro first head
                    subst char
                    cases chars with
                    | nil => simp at head
                    | cons next chars =>
                      have : next = '*' := by simpa using head
                      subst next
                      simp at notBlock
                  obtain ⟨remaining, tokenRead, finish⟩ := bind_ok parsed
                  have same := Except.ok.inj finish
                  subst tokens
                  exact .punctuation symbol boundary (ih tokenRead)
                · contradiction

end Parser.EBNF.Reader

namespace Parser.EBNF

theorem lex_sound (parsed : lex source = .ok tokens) : Metalanguage.Lexes source.toList tokens :=
  Reader.tokenize_sound parsed

theorem lex_iff : lex source = .ok tokens ↔ Metalanguage.Lexes source.toList tokens :=
  ⟨lex_sound, lex_complete⟩

end Parser.EBNF
