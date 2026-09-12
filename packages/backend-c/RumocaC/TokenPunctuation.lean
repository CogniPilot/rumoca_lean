import RumocaC.TokenStarts

/-! Punctuator competition with identifiers, numbers and literals. The finite
C11 catalog supplies only local head facts; the proofs quantify over every
actual continuation. No executable scanning path is introduced. -/
namespace Rumoca.CTokens.Competition

private def safeHead (chars : List Char) : Bool :=
  match chars with
  | [] => false
  | c :: _ => !CLexical.identifierCharacter c && c != '"' && c != '\''

theorem punctuator_starts (member : spelling ∈ CPunctuator.spellings) :
    Starts (fun c => CLexical.identifierCharacter c = false ∧ c ≠ '"' ∧ c ≠ '\'') spelling.toList := by
  have catalog : ∀ word ∈ CPunctuator.spellings, safeHead word.toList = true := by decide +kernel
  have checked := catalog spelling member
  cases chars : spelling.toList with
  | nil => simp [chars, safeHead] at checked
  | cons c cs =>
      refine ⟨c, cs, rfl, ?_⟩
      simpa [chars, safeHead, and_assoc] using checked

theorem punctuator_input_starts (token : Consumes input (.punctuator spelling) rest) :
    Starts (fun c => CLexical.identifierCharacter c = false ∧ c ≠ '"' ∧ c ≠ '\'') input := by
  cases token with
  | punctuator read safe =>
      rw [read.text]
      exact (punctuator_starts read.member).append _

/-- Inspect only the characters present in a punctuator spelling. A single
dot requires the separate following-character premise from PunctuationSafe. -/
private def blocksNumber : List Char → Bool
  | [] => false
  | c :: rest => if c == '.' then
      match rest with
      | [] => false
      | next :: _ => !next.isDigit
    else !c.isDigit

private theorem blocksNumber_sound (checked : blocksNumber chars = true) (rest : List Char) :
    ¬ NumberStart (chars ++ rest) := by
  cases chars with
  | nil => simp [blocksNumber] at checked
  | cons c cs =>
      by_cases dot : c = '.'
      · subst c
        cases cs with
        | nil => simp [blocksNumber] at checked
        | cons c cs =>
            simp only [blocksNumber, beq_self_eq_true, ↓reduceIte, Bool.not_eq_true'] at checked
            intro number
            cases number with
            | digit digit => contradiction
            | dotDigit digit => simp [checked] at digit
      · have notDigit : c.isDigit = false := by simpa [blocksNumber, dot] using checked
        intro number
        rcases number.first.head with digit | same
        · simp [notDigit] at digit
        · exact dot same

theorem punctuator_before_number (member : spelling ∈ CPunctuator.spellings)
    (included : spelling.toList <+: input) (number : NumberStart input) : spelling = "." := by
  have catalog : ∀ word ∈ CPunctuator.spellings,
      word = "." ∨ blocksNumber word.toList = true := by decide +kernel
  rcases catalog spelling member with same | blocked
  · exact same
  · obtain ⟨rest, rfl⟩ := included
    exact False.elim (blocksNumber_sound blocked rest number)

theorem punctuator_not_number (punctuation : Consumes input (.punctuator spelling) rest)
    (number : NumberStart input) : False := by
  cases punctuation with
  | punctuator read safe =>
      have catalog : ∀ word ∈ CPunctuator.spellings,
          word = "." ∨ blocksNumber word.toList = true := by decide +kernel
      rw [read.text] at number
      rcases catalog spelling read.member with rfl | blocked
      · change NumberStart ('.' :: rest) at number
        cases number with
        | digit digit => contradiction
        | @dotDigit c cs digit =>
            have forbidden := safe.1 rfl c cs rfl
            simp [forbidden] at digit
      · exact blocksNumber_sound blocked rest number

end Rumoca.CTokens.Competition
