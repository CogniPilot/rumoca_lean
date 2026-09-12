import RumocaC.Decimal
import RumocaC.LexicalCharacters
import Parser.Scanner.Prefix

/-! Independent preprocessing-number candidates for C11 N1570 §6.4.8.
Universal names follow §6.4.3 syntax; their code-point constraints are not needed
for the boundary theorem. The extension constructor conservatively includes
every character outside the basic source set (§§5.2.1,6.4.2.1), rather than
assuming a particular implementation's identifier extensions. Thus maximality
is checked against an envelope of the permitted preprocessing numbers.

This is a declarative grammar, not a scanner/compiler pass. Preprocessing
numbers have no type or value. The decimal value relation and later integer
typing/range constraints are separate. -/
namespace Rumoca.CPPNumber
open _root_.Parser CLexical

inductive Spells : List Char → Prop where
  | digit : c.isDigit = true → Spells [c]
  | dotDigit : c.isDigit = true → Spells ['.', c]
  | appendDigit : Spells text → c.isDigit = true → Spells (text ++ [c])
  | appendNondigit : Spells text → Nondigit chars → Spells (text ++ chars)
  | exponent : Spells text → letter ∈ ['e', 'E', 'p', 'P'] → sign ∈ ['+', '-'] →
      Spells (text ++ [letter, sign])
  | dot : Spells text → Spells (text ++ ['.'])

/-- A conservative set of characters occurring in preprocessing numbers.
The grammar still restricts where signs and universal names may occur. -/
def character (c : Char) : Bool :=
  identRest c || ['.', '+', '-', '\\'].contains c || !basicSource c

private theorem digit_character (digit : c.isDigit = true) : character c = true := by
  simp [character, identRest, digit]

private theorem identifier_character (word : identifierCharacter c = true) : character c = true := by
  simp only [identifierCharacter, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at word
  rcases word with (word | rfl) | outside
  · simp [character, word]
  · decide +kernel
  · simp [character, outside]

theorem Spells.characters (number : Spells text) :
    ∀ c ∈ text, character c = true := by
  induction number with
  | digit digit =>
      intro c member
      simp only [List.mem_singleton] at member
      subst c
      exact digit_character digit
  | dotDigit digit =>
      intro c member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · decide +kernel
      · exact digit_character digit
  | appendDigit number digit ih =>
      intro c member
      rcases List.mem_append.mp member with before | after
      · exact ih c before
      · simp only [List.mem_singleton] at after
        subst c
        exact digit_character digit
  | appendNondigit number word ih =>
      intro c member
      rcases List.mem_append.mp member with before | after
      · exact ih c before
      · exact identifier_character (word.characters c after)
  | exponent number letter sign ih =>
      intro c member
      rcases List.mem_append.mp member with before | after
      · exact ih c before
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at after
        rcases after with rfl | rfl
        · have all : ∀ c ∈ ['e', 'E', 'p', 'P'], character c = true := by decide +kernel
          exact all _ letter
        · have all : ∀ c ∈ ['+', '-'], character c = true := by decide +kernel
          exact all _ sign
  | dot number ih =>
      intro c member
      rcases List.mem_append.mp member with before | after
      · exact ih c before
      · simp only [List.mem_singleton] at after
        subst c
        decide +kernel

theorem Spells.append_digits (number : Spells text) (digits : List Char)
    (all : digits.all Char.isDigit = true) : Spells (text ++ digits) := by
  induction digits generalizing text with
  | nil => simpa using number
  | cons c cs ih =>
      simp only [List.all_cons, Bool.and_eq_true] at all
      simpa only [List.append_assoc, List.singleton_append] using
        ih (Spells.appendDigit number all.1) all.2

theorem natural_spells (n : Nat) : Spells (toString n).toList := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  have nonempty := Nat.length_toDigits_pos (b := 10) (n := n)
  cases chars : Nat.toDigits 10 n with
  | nil => simp [chars] at nonempty
  | cons c cs =>
      have all : (c :: cs).all Char.isDigit = true := by
        apply List.all_eq_true.mpr
        intro d member
        exact Nat.isDigit_of_mem_toDigits (by decide +kernel) (by decide +kernel) (chars ▸ member)
      simp only [List.all_cons, Bool.and_eq_true] at all
      exact (Spells.digit all.1).append_digits cs all.2

/-- A selected decimal token consumes exactly this prefix, and no longer
candidate preprocessing number can match the actual input. -/
structure Consumes (input text : List Char) (value : Nat) (rest : List Char) : Prop where
  spelling : Spells text
  denotes : CDecimal.Denotes text value
  input_eq : input = text ++ rest
  longest : ∀ candidate, Spells candidate → candidate <+: input → candidate.length ≤ text.length

theorem natural_consumes (n : Nat) (stop : character marker = false) (rest : List Char) :
    Consumes ((toString n).toList ++ marker :: rest) (toString n).toList n (marker :: rest) := by
  refine ⟨natural_spells n, CDecimal.render_denotes n, rfl, ?_⟩
  intro candidate number starts
  apply Scanner.prefix_before_delimiter starts
  intro member
  have present := number.characters marker member
  simp [stop] at present

theorem consumes_unique (first : Consumes input a x restA) (second : Consumes input b y restB) :
    a = b ∧ x = y ∧ restA = restB := by
  have pa : a <+: input := ⟨restA, first.input_eq.symm⟩
  have pb : b <+: input := ⟨restB, second.input_eq.symm⟩
  have same : a = b :=
    (List.prefix_of_prefix_length_le pa pb (second.longest a first.spelling pa)).eq_of_length_le
      (first.longest b second.spelling pb)
  refine ⟨same, ?_, ?_⟩
  · exact CDecimal.denotes_unique (same ▸ first.denotes) second.denotes
  · have texts := first.input_eq.symm.trans second.input_eq
    simpa only [same, List.append_cancel_left_eq] using texts

end Rumoca.CPPNumber
