import RumocaC.TokenCandidates
import RumocaC.TokenPunctuation

/-! Cross-category longest-token proofs for the existing token judgments.
The competing vocabulary is the independent normal-context C11 envelope.
No candidate must have come from the printer, and every prefix comparison
retains the actual input and continuation. -/
namespace Rumoca.CTokens.Normal
open Competition

theorem Spelling.candidate (spelled : Spelling token chars) : Candidate chars := by
  cases spelled with
  | word parts => exact .identifier (CIdentifierToken.word_spells parts)
  | number number => exact .number number
  | string literal => exact .string (CString.denotes_quoted literal)
  | punctuator member => exact .punctuator member

theorem Spelling.positive (spelled : Spelling token chars) : 0 < chars.length := by
  cases spelled with
  | word parts => exact (identifier_starts (CIdentifierToken.word_spells parts)).positive
  | number number => exact (number_starts number).first.positive
  | string literal => exact (quoted_starts (CString.denotes_quoted literal)).positive
  | punctuator member => exact (punctuator_starts member).positive

end Rumoca.CTokens.Normal

namespace Rumoca.CTokens.Competition
open Normal (Candidate Spelling Longest)

private theorem word_identifier_start (word : Consumes input (.word name) rest) :
    Starts IdentifierStart input := by
  obtain ⟨first, tail, rfl, valid⟩ := word_starts word
  exact ⟨first, tail, rfl, Or.inl valid⟩

private theorem identifier_punctuator (word : Starts IdentifierStart input)
    (punctuation : Starts (fun c => CLexical.identifierCharacter c = false ∧ c ≠ '"' ∧ c ≠ '\'') input) : False :=
  word.disjoint punctuation (fun _ start safe => by simp [start.character] at safe)

private theorem identifier_marker (word : Starts IdentifierStart input)
    (mark : Starts (fun c => c = marker) input) (bad : CLexical.identifierCharacter marker = false) : False := by
  apply word.disjoint mark
  intro c start same
  subst c
  have good := start.character
  simp [bad] at good

private theorem number_marker (number : NumberStart input) (mark : Starts (fun c => c = marker) input)
    (digit : marker.isDigit = false) (dot : marker ≠ '.') : False := by
  apply number.first.disjoint mark
  intro c numeric same
  subst c
  rcases numeric with good | same
  · simp [digit] at good
  · exact dot same

private theorem punctuator_marker
    (punctuation : Starts (fun c => CLexical.identifierCharacter c = false ∧ c ≠ '"' ∧ c ≠ '\'') input)
    (mark : Starts (fun c => c = marker) input) (quote : marker ∈ ['"', '\'']) : False := by
  apply punctuation.disjoint mark
  intro c safe same
  subst c
  simp only [List.mem_cons, List.not_mem_nil, or_false] at quote
  rcases quote with rfl | rfl
  · exact safe.2.1 rfl
  · exact safe.2.2 rfl

private theorem character_starts (included : '\'' :: chars <+: input) : Starts (fun c => c = '\'') input :=
  (show Starts (fun c => c = '\'') ('\'' :: chars) from ⟨_, _, rfl, rfl⟩).prefix included

theorem word_longest (word : Consumes input (.word name) rest) : Longest input name.toList := by
  cases word with
  | word parts read safe =>
      have actual : Consumes input (.word name) rest := .word parts read safe
      have first := word_identifier_start actual
      intro chars candidate included
      cases candidate with
      | identifier identifier => exact read.longest _ identifier included
      | number number => exact False.elim (word_not_number actual number included)
      | string string =>
          exact False.elim (identifier_marker first ((quoted_starts string).prefix included) (by decide +kernel))
      | encoded encoding quote => exact False.elim (word_not_encoded actual encoding quote included)
      | character => exact False.elim (identifier_marker first (character_starts included) (by decide +kernel))
      | punctuator member => exact False.elim (identifier_punctuator first ((punctuator_starts member).prefix included))
      | singleton c => exact Spelling.positive (.word parts)

theorem number_longest (number : Consumes input (.number spelling) rest) : Longest input spelling.toList := by
  cases number with
  | number spelled inputEq longest =>
      have actual : Consumes input (.number spelling) rest := .number spelled inputEq longest
      have first := number_input_starts actual
      intro chars candidate included
      cases candidate with
      | identifier identifier =>
          exact False.elim (number_start_not_identifier first ((identifier_starts identifier).prefix included))
      | number number => exact longest _ number included
      | string string =>
          exact False.elim (number_marker first ((quoted_starts string).prefix included) (by decide +kernel) (by decide +kernel))
      | encoded encoding quote =>
          exact False.elim (number_start_not_identifier first ((encoded_starts encoding _).prefix included))
      | character =>
          exact False.elim (number_marker first (character_starts included) (by decide +kernel) (by decide +kernel))
      | punctuator member =>
          have onlyDot := punctuator_before_number member included first
          subst onlyDot
          exact Spelling.positive (.number spelled)
      | singleton c => exact Spelling.positive (.number spelled)

theorem string_longest (literal : CString.Denotes text bytes) (inputEq : input = text ++ rest) :
    Longest input text := by
  have quoted := CString.denotes_quoted literal
  have first : Starts (fun c => c = '"') input := inputEq ▸ (quoted_starts quoted).append rest
  intro chars candidate included
  cases candidate with
  | identifier identifier =>
      exact False.elim (identifier_marker ((identifier_starts identifier).prefix included) first (by decide +kernel))
  | number number =>
      exact False.elim (number_marker ((number_starts number).prefix included) first (by decide +kernel) (by decide +kernel))
  | string string =>
      obtain ⟨remaining, same⟩ := included
      have equal := quoted.boundary_unique string (inputEq.symm.trans same.symm)
      exact (congrArg List.length equal.1).symm.le
  | encoded encoding quote =>
      exact False.elim (identifier_marker ((encoded_starts encoding _).prefix included) first (by decide +kernel))
  | character =>
      apply False.elim
      exact first.disjoint (character_starts included) (by intro c h q; subst c; contradiction)
  | punctuator member =>
      exact False.elim (punctuator_marker ((punctuator_starts member).prefix included) first (by simp))
  | singleton c => exact Spelling.positive (.string literal)

theorem punctuator_longest (punctuation : Consumes input (.punctuator spelling) rest) :
    Longest input spelling.toList := by
  cases punctuation with
  | punctuator read safe =>
      have actual : Consumes input (.punctuator spelling) rest := .punctuator read safe
      have first := punctuator_input_starts actual
      intro chars candidate included
      cases candidate with
      | identifier identifier => exact False.elim (identifier_punctuator ((identifier_starts identifier).prefix included) first)
      | number number => exact False.elim (punctuator_not_number actual ((number_starts number).prefix included))
      | string string => exact False.elim (punctuator_marker first ((quoted_starts string).prefix included) (by simp))
      | encoded encoding quote => exact False.elim (identifier_punctuator ((encoded_starts encoding _).prefix included) first)
      | character => exact False.elim (punctuator_marker first (character_starts included) (by simp))
      | punctuator member => exact read.longest _ member included
      | singleton c => exact Spelling.positive (.punctuator read.member)

end Rumoca.CTokens.Competition
