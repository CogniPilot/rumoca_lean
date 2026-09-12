import Parser.EBNF.LexicalProofs

/-! Every independently specified EBNF character stream is tokenized within
the actual character-count budget. No successful-lexing premise is supplied. -/
namespace Parser.EBNF.Reader
open Metalanguage

private theorem ident_ne (starts : identStart char = true) (other : identStart symbol = false) :
    char ≠ symbol := by
  intro equal
  subst char
  rw [other] at starts
  contradiction

theorem tokenize_complete (valid : Lexes chars tokens) (budget : chars.length + 1 ≤ fuel) :
    tokenize fuel chars = .ok tokens := by
  induction valid generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at budget
    | succ fuel => rfl
  | @space char chars tokens white rest ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have read := ih (fuel := fuel) (by simp only [List.length_cons] at budget; omega)
      simp [tokenize, white, read]
  | @block body chars tokens bodyValid rest ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have read := ih (fuel := fuel) (by
        simp only [List.length_cons, List.length_append] at budget
        omega)
      have skipped := comment_complete (rest := chars) bodyValid
      simp [tokenize, asciiSpace, skipped, read, bind, Except.bind]
  | @line body chars tokens bodyValid boundary rest ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have read := ih (fuel := fuel) (by
        simp only [List.length_cons, List.length_append] at budget
        omega)
      have skipped := line_complete bodyValid boundary
      simp [tokenize, asciiSpace, skipped, read]
  | @quoted delimiter body chars tokens quote bodyValid rest ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have read := ih (fuel := fuel) (by
        simp only [List.length_cons, List.length_append] at budget
        omega)
      have ordinary : delimiter ≠ '\\' := by rcases quote with rfl | rfl <;> decide
      have literal := quoted_complete (rest := chars) bodyValid ordinary
      rcases quote with rfl | rfl <;>
        simp [tokenize, asciiSpace, literal, read, bind, Except.bind, pure, Except.pure]
  | @name first tail chars tokens bodyValid rest ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have read := ih (fuel := fuel) (by
        simp only [List.length_cons, List.length_append] at budget
        omega)
      have ordinary : ∀ {symbol}, identStart symbol = false → first ≠ symbol :=
        fun {_} other => ident_ne bodyValid.1 other
      have space : asciiSpace first = false := by
        simp [asciiSpace, ordinary (symbol := ' ') (by decide),
          ordinary (symbol := '\t') (by decide), ordinary (symbol := '\r') (by decide),
          ordinary (symbol := '\n') (by decide)]
      have openParen := ordinary (symbol := '(') (by decide)
      have slash := ordinary (symbol := '/') (by decide)
      have doubleQuote := ordinary (symbol := '"') (by decide)
      have singleQuote := ordinary (symbol := '\'') (by decide)
      have word := name_complete bodyValid
      simp [tokenize, space, openParen, slash, doubleQuote, singleQuote, bodyValid.1,
        word.1, read, bind, Except.bind, pure, Except.pure]
  | @punctuation char chars tokens symbol boundary rest ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have read := ih (fuel := fuel) (by simp only [List.length_cons] at budget; omega)
      have noComment : (char :: chars).take 2 ≠ ['(', '*'] := by
        intro same
        cases chars with
        | nil => simp at same
        | cons next chars =>
          have parts : char = '(' ∧ next = '*' := by simpa using same
          exact boundary parts.1 (by simpa using parts.2)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at symbol
      rcases symbol with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all [tokenize, asciiSpace, identStart, asciiLetter,
          bind, Except.bind, pure, Except.pure]

end Parser.EBNF.Reader

namespace Parser.EBNF

theorem lex_complete (valid : Metalanguage.Lexes source.toList tokens) :
    lex source = .ok tokens :=
  Reader.tokenize_complete valid (Nat.le_refl _)

end Parser.EBNF
