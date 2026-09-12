import RumocaC.Identifier

/-! Shared C11 source-character and identifier-nondigit candidates. Universal
names follow N1570 §6.4.3 syntax. Their code-point constraints are not needed
for maximal-token boundary proofs. Extension candidates conservatively include
all characters outside the basic source set (§§5.2.1,6.4.2.1); this does not
claim that a particular implementation accepts all such identifiers. -/
namespace Rumoca.CLexical
open _root_.Parser

/-- C's basic source characters in the authored ASCII encoding profile. -/
def basicSource (c : Char) : Bool := identRest c ||
  ['{', '}', '[', ']', '#', '(', ')', '<', '>', '%', ':', ';', '.', '?', '*', '+', '-',
    '/', '^', '&', '|', '~', '!', '=', ',', '\\', '"', '\'', ' ', '\t', '\n', '\r',
    Char.ofNat 11, Char.ofNat 12].contains c

def hexadecimal (c : Char) : Bool :=
  c.isDigit || (decide ('a' ≤ c) && decide (c ≤ 'f')) ||
    (decide ('A' ≤ c) && decide (c ≤ 'F'))

inductive Nondigit : List Char → Prop where
  | basic : identStart c = true → Nondigit [c]
  | universal4 : digits.length = 4 → digits.all hexadecimal = true →
      Nondigit ('\\' :: 'u' :: digits)
  | universal8 : digits.length = 8 → digits.all hexadecimal = true →
      Nondigit ('\\' :: 'U' :: digits)
  | extension : basicSource c = false → Nondigit [c]

/-- Characters occurring in identifier candidates, including universal names. -/
def identifierCharacter (c : Char) : Bool := identRest c || c == '\\' || !basicSource c

theorem identStart_not_digit (word : identStart c = true) : c.isDigit = false := by
  apply Bool.eq_false_iff.mpr
  intro digit
  have bounds : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
    simpa only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] using digit
  simp only [identStart, asciiLetter, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at word
  rcases word with (lower | upper) | rfl
  · have low : 97 ≤ c.toNat := lower.1
    omega
  · have low : 65 ≤ c.toNat := upper.1
    omega
  · simp at bounds

private theorem hexadecimal_character (hex : hexadecimal c = true) :
    identifierCharacter c = true := by
  simp only [hexadecimal, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hex
  rcases hex with (digit | lower) | upper
  · simp [identifierCharacter, identRest, digit]
  · have letter : asciiLetter c = true := by
      simp only [asciiLetter, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inl ⟨lower.1, Char.le_trans lower.2 (by decide +kernel)⟩
    simp [identifierCharacter, identRest, identStart, letter]
  · have letter : asciiLetter c = true := by
      simp only [asciiLetter, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨upper.1, Char.le_trans upper.2 (by decide +kernel)⟩
    simp [identifierCharacter, identRest, identStart, letter]

theorem Nondigit.characters (word : Nondigit chars) :
    ∀ c ∈ chars, identifierCharacter c = true := by
  cases word with
  | basic starts =>
      intro c member
      simp only [List.mem_singleton] at member
      subst c
      simp [identifierCharacter, identRest, starts]
  | extension outside =>
      intro c member
      simp only [List.mem_singleton] at member
      subst c
      simp [identifierCharacter, outside]
  | universal4 size digits | universal8 size digits =>
      intro c member
      simp only [List.mem_cons] at member
      rcases member with rfl | rfl | member
      · decide +kernel
      · decide +kernel
      · exact hexadecimal_character (List.all_eq_true.mp digits c member)

end Rumoca.CLexical
