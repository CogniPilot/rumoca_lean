import RumocaFMI3.Identifier
import XML.Syntax

namespace Rumoca.FMI3
open _root_.Parser

/-- Lexical word shape, without excluding source-language or C keywords. -/
def NameParts (name : String) : Prop :=
  ∃ c cs, name.toList = c :: cs ∧ identStart c = true ∧ cs.all identRest = true

private theorem identifier_text_char {c : Char} (h : identRest c = true) : XML.TextChar c := by
  simp only [identRest, identStart, asciiLetter, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq, Char.isDigit, Char.le_def, UInt32.le_iff_toNat_le] at h
  unfold XML.TextChar Char.toNat
  rcases h with (((a | a) | rfl) | a)
  · change 97 ≤ c.val.toNat ∧ c.val.toNat ≤ 122 at a
    exact ⟨by omega, by omega⟩
  · change 65 ≤ c.val.toNat ∧ c.val.toNat ≤ 90 at a
    exact ⟨by omega, by omega⟩
  · decide +kernel
  · change 48 ≤ c.val.toNat ∧ c.val.toNat ≤ 57 at a
    exact ⟨by omega, by omega⟩

theorem NameParts.text (h : NameParts name) : XML.Text name := by
  obtain ⟨c, cs, chars, head, rest⟩ := h
  intro d hd
  rw [chars] at hd
  rcases List.mem_cons.mp hd with rfl | tail
  · exact identifier_text_char (by simp [identRest, head])
  · exact identifier_text_char (List.all_eq_true.mp rest d tail)

theorem modelIdentifier_parts (h : NameParts name) : NameParts (modelIdentifier name) := by
  obtain ⟨c, cs, chars, head, rest⟩ := h
  refine ⟨'R', ['u', 'm', 'o', 'c', 'a', '_'] ++ c :: cs, ?_, by decide +kernel, ?_⟩
  · simp [modelIdentifier, String.toList_append, chars]
  · have hc : identRest c = true := by simp [identRest, head]
    simp only [List.all_append, List.all_cons, List.all_nil, hc, rest]
    rfl

theorem modelIdentifier_valid (h : NameParts name) :
    CIdentifier.valid [] (modelIdentifier name) = true := by
  have noR : ∀ word ∈ CIdentifier.keywords, word.toList.head? ≠ some 'R' := by decide +kernel
  have not_keyword : modelIdentifier name ∉ CIdentifier.keywords := by
    intro mem
    exact noR _ mem (by simp [modelIdentifier, String.toList_append])
  obtain ⟨c, cs, chars, head, rest⟩ := modelIdentifier_parts h
  simp [CIdentifier.valid, chars, head, rest, not_keyword]

theorem modelIdentifier_injective : Function.Injective modelIdentifier := by
  intro a b h
  have he := congrArg String.toList h
  simp only [modelIdentifier, String.toList_append, List.append_right_inj] at he
  exact String.toList_injective he

theorem functionPrefix_word (h : NameParts name) :
    CIdentifier.valid [] (modelIdentifier name ++ "_") = true := by
  have parts : NameParts (name ++ "_") := by
    obtain ⟨c, cs, chars, head, rest⟩ := h
    refine ⟨c, cs ++ ['_'], ?_, head, ?_⟩
    · simp [String.toList_append, chars]
    · simp [rest, identRest, identStart, asciiLetter]
  simpa [modelIdentifier, String.append_assoc] using modelIdentifier_valid parts

end Rumoca.FMI3
