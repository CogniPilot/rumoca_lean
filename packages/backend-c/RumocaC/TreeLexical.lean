import RumocaC.Identifier
import Init.Data.Nat.ToString

/-! Lexical profile for the structured adapter's C expressions. Longest-match
symbols share prefixes. Decimal constants and identifiers are separate from
the token grammar; comments, macros and whole-file preprocessing are separate. -/
namespace Rumoca.CTree.Syntax
open _root_.Parser

def numberRest (c : Char) : Bool := identRest c || c == '.'

def config : Scanner.Config where
  wordStart := identStart
  wordRest := identRest
  numberRest := numberRest
  classify := Token.literal
  single := fun c => ['(', ')', '{', '}', '[', ']', '*', ';', '=', '+', '<', '>',
    ',', '!', '&', '|', '-', '.'].contains c
  pair := fun c =>
    if ['=', '!', '<', '>'].contains c then some '='
    else if c == '&' then some '&'
    else if c == '|' then some '|'
    else if c == '-' then some '>'
    else none

theorem lex_identifier (name : String) (valid : CIdentifier.valid reserved name = true)
    (c : Char) (rest : List Char) (ts : List Token)
    (stop : identRest c = false) (tail : Scanner.Lexes config (c :: rest) ts) :
    Scanner.Lexes config (name.toList ++ c :: rest) (.literal name :: ts) :=
  CIdentifier.lex_word config rfl rfl rfl rfl name c rest ts
    (CIdentifier.word_parts reserved name valid) stop tail

private theorem digit_properties (digit : c.isDigit = true) :
    asciiSpace c = false ∧ identStart c = false ∧ numberRest c = true := by
  have bounds : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
    simpa only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] using digit
  have different (d : Char) (outside : d.toNat < 48 ∨ 57 < d.toNat) : c ≠ d := by
    intro same
    subst c
    omega
  have notWord : identStart c = false := by
    simp only [identStart, asciiLetter, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
      decide_eq_false_iff_not, beq_eq_false_iff_ne]
    change ((¬ (97 ≤ c.toNat) ∨ ¬ (c.toNat ≤ 122)) ∧
      (¬ (65 ≤ c.toNat) ∨ ¬ (c.toNat ≤ 90))) ∧ c ≠ '_'
    exact ⟨⟨Or.inl (by omega), Or.inl (by omega)⟩, different '_' (by decide +kernel)⟩
  refine ⟨?_, notWord, ?_⟩
  · simp [asciiSpace, different ' ' (by decide +kernel), different '\t' (by decide +kernel),
      different '\r' (by decide +kernel), different '\n' (by decide +kernel)]
  · simp [numberRest, identRest, digit]

private theorem take_digits (digits : List Char) (all : digits.all Char.isDigit = true)
    (c : Char) (rest : List Char) (stop : numberRest c = false) :
    (digits ++ c :: rest).takeWhile numberRest = digits ∧
      (digits ++ c :: rest).dropWhile numberRest = c :: rest := by
  induction digits with
  | nil => simp [stop]
  | cons d ds ih =>
      simp only [List.all_cons, Bool.and_eq_true] at all
      obtain ⟨take, drop⟩ := ih all.2
      simp [((digit_properties all.1).2.2), take, drop]

theorem lex_natural (n : Nat) (c : Char) (rest : List Char) (ts : List Token)
    (stop : numberRest c = false) (tail : Scanner.Lexes config (c :: rest) ts) :
    Scanner.Lexes config ((toString n).toList ++ c :: rest) (.literal (toString n) :: ts) := by
  have nonempty := Nat.length_toDigits_pos (b := 10) (n := n)
  cases digits : Nat.toDigits 10 n with
  | nil => simp [digits] at nonempty
  | cons first remaining =>
      have all : (first :: remaining).all Char.isDigit = true := by
        apply List.all_eq_true.mpr
        intro d member
        exact Nat.isDigit_of_mem_toDigits (by decide +kernel) (by decide +kernel) (digits ▸ member)
      have digitsAll : first.isDigit = true ∧ remaining.all Char.isDigit = true := by
        simpa only [List.all_cons, Bool.and_eq_true] using all
      have facts := digit_properties digitsAll.1
      obtain ⟨take, drop⟩ := take_digits remaining digitsAll.2 c rest stop
      have step := Scanner.Lexes.number (cfg := config) (c := first)
        (cs := remaining ++ c :: rest) facts.1 facts.2.1 digitsAll.1
        (by simpa only [config, drop] using tail)
      simpa only [Nat.toString_eq_ofList_toDigits, digits, String.toList_ofList,
        config, take, List.cons_append] using step

end Rumoca.CTree.Syntax
