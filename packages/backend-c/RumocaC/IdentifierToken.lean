import RumocaC.LexicalCharacters
import Parser.Scanner.Prefix

/-! Identifier preprocessing-token candidates and exact ASCII word boundaries.
N1570 §6.4.2.1 supplies the grammar. Keywords are classified later in phase 7;
an encoded string prefix adjoining a quote is a separate competing category.
This declarative relation is not an executable C reader. -/
namespace Rumoca.CIdentifierToken
open _root_.Parser CLexical

inductive Spells : List Char → Prop where
  | first : Nondigit text → Spells text
  | appendNondigit : Spells text → Nondigit chars → Spells (text ++ chars)
  | appendDigit : Spells text → c.isDigit = true → Spells (text ++ [c])

theorem Spells.characters (identifier : Spells text) :
    ∀ c ∈ text, identifierCharacter c = true := by
  induction identifier with
  | first word => exact word.characters
  | appendNondigit identifier word ih =>
      intro c member
      rcases List.mem_append.mp member with before | after
      · exact ih c before
      · exact word.characters c after
  | appendDigit identifier digit ih =>
      intro c member
      rcases List.mem_append.mp member with before | after
      · exact ih c before
      · simp only [List.mem_singleton] at after
        subst c
        simp [identifierCharacter, identRest, digit]

theorem Spells.append_ascii (identifier : Spells text) (chars : List Char)
    (all : chars.all identRest = true) : Spells (text ++ chars) := by
  induction chars generalizing text with
  | nil => simpa using identifier
  | cons c cs ih =>
      simp only [List.all_cons, Bool.and_eq_true] at all
      have next : Spells (text ++ [c]) := by
        rcases (show identStart c = true ∨ c.isDigit = true from
          by simpa only [identRest, Bool.or_eq_true] using all.1) with start | digit
        · exact .appendNondigit identifier (.basic start)
        · exact .appendDigit identifier digit
      simpa only [List.append_assoc, List.singleton_append] using ih next all.2

/-- ASCII word syntax is shared by identifiers, typedef names and keywords. -/
def WordParts (name : String) : Prop :=
  ∃ first rest, name.toList = first :: rest ∧ identStart first = true ∧ rest.all identRest = true

theorem word_spells (parts : WordParts name) : Spells name.toList := by
  obtain ⟨c, cs, text, start, tail⟩ := parts
  rw [text]
  exact (Spells.first (.basic start)).append_ascii cs tail

structure Consumes (input : List Char) (name : String) (rest : List Char) : Prop where
  spelling : Spells name.toList
  input_eq : input = name.toList ++ rest
  longest : ∀ candidate, Spells candidate → candidate <+: input → candidate.length ≤ name.toList.length

theorem word_consumes (parts : WordParts name) (stop : identifierCharacter marker = false)
    (rest : List Char) : Consumes (name.toList ++ marker :: rest) name (marker :: rest) := by
  refine ⟨word_spells parts, rfl, ?_⟩
  intro candidate identifier starts
  apply Scanner.prefix_before_delimiter starts
  intro member
  have present := identifier.characters marker member
  simp [stop] at present

theorem identifier_consumes (valid : CIdentifier.valid typedefs name = true)
    (stop : identifierCharacter marker = false) (rest : List Char) :
    Consumes (name.toList ++ marker :: rest) name (marker :: rest) :=
  word_consumes (CIdentifier.word_parts typedefs name valid) stop rest

theorem consumes_unique (first : Consumes input a restA) (second : Consumes input b restB) :
    a = b ∧ restA = restB := by
  have pa : a.toList <+: input := ⟨restA, first.input_eq.symm⟩
  have pb : b.toList <+: input := ⟨restB, second.input_eq.symm⟩
  have same : a.toList = b.toList :=
    (List.prefix_of_prefix_length_le pa pb (second.longest a.toList first.spelling pa)).eq_of_length_le
      (first.longest b.toList second.spelling pb)
  have names : a = b := by simpa using congrArg String.ofList same
  refine ⟨names, ?_⟩
  have texts := first.input_eq.symm.trans second.input_eq
  simpa only [names, List.append_cancel_left_eq] using texts

end Rumoca.CIdentifierToken
