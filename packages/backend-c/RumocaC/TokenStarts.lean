import RumocaC.Tokens

/-! Head-shape and competing-category facts for C11 preprocessing tokens.
These proofs use the actual continuation and the independent token grammars;
no executable C lexer or parser is introduced. -/
namespace Rumoca.CTokens.Competition

def Starts (allowed : Char → Prop) (chars : List Char) : Prop :=
  ∃ first rest, chars = first :: rest ∧ allowed first

theorem Starts.append (start : Starts allowed chars) (suffix : List Char) :
    Starts allowed (chars ++ suffix) := by
  obtain ⟨first, rest, rfl, member⟩ := start
  exact ⟨first, rest ++ suffix, rfl, member⟩

theorem Starts.prefix (start : Starts allowed chars) (included : chars <+: input) :
    Starts allowed input := by
  obtain ⟨suffix, rfl⟩ := included
  exact start.append suffix

theorem Starts.head (start : Starts allowed (first :: rest)) : allowed first := by
  obtain ⟨head, tail, same, member⟩ := start
  exact (List.cons.inj same).1 ▸ member

theorem Starts.disjoint (left : Starts p input) (right : Starts q input)
    (incompatible : ∀ c, p c → q c → False) : False := by
  obtain ⟨first, tail, rfl, valid⟩ := left
  exact incompatible first valid right.head

theorem Starts.positive (start : Starts allowed input) : 0 < input.length := by
  obtain ⟨first, tail, rfl, member⟩ := start
  simp

def IdentifierStart (c : Char) : Prop :=
  _root_.Parser.identStart c = true ∨ c = '\\' ∨ CLexical.basicSource c = false

theorem nondigit_starts (token : CLexical.Nondigit chars) : Starts IdentifierStart chars := by
  cases token with
  | basic start => exact ⟨_, [], rfl, Or.inl start⟩
  | universal4 size hexadecimal => exact ⟨_, _, rfl, Or.inr (Or.inl rfl)⟩
  | universal8 size hexadecimal => exact ⟨_, _, rfl, Or.inr (Or.inl rfl)⟩
  | extension outside => exact ⟨_, [], rfl, Or.inr (Or.inr outside)⟩

theorem identifier_starts (token : CIdentifierToken.Spells chars) : Starts IdentifierStart chars := by
  induction token with
  | first first => exact nondigit_starts first
  | appendNondigit token next ih => exact ih.append _
  | appendDigit token digit ih => exact ih.append _

theorem IdentifierStart.not_digit (start : IdentifierStart c) : c.isDigit = false := by
  rcases start with basic | rfl | outside
  · exact CLexical.identStart_not_digit basic
  · decide +kernel
  · apply Bool.eq_false_iff.mpr
    intro digit
    simp [CLexical.basicSource, _root_.Parser.identRest, digit] at outside

theorem IdentifierStart.character (start : IdentifierStart c) : CLexical.identifierCharacter c = true := by
  rcases start with basic | rfl | outside
  · simp [CLexical.identifierCharacter, _root_.Parser.identRest, basic]
  · decide +kernel
  · simp [CLexical.identifierCharacter, outside]

inductive NumberStart : List Char → Prop where
  | digit : c.isDigit = true → NumberStart (c :: rest)
  | dotDigit : c.isDigit = true → NumberStart ('.' :: c :: rest)

theorem NumberStart.append (start : NumberStart chars) (suffix : List Char) :
    NumberStart (chars ++ suffix) := by
  cases start with
  | digit digit => exact .digit digit
  | dotDigit digit => exact .dotDigit digit

theorem NumberStart.prefix (start : NumberStart chars) (included : chars <+: input) : NumberStart input := by
  obtain ⟨suffix, rfl⟩ := included
  exact start.append suffix

theorem NumberStart.first (number : NumberStart input) : Starts (fun c => c.isDigit = true ∨ c = '.') input := by
  cases number with
  | digit digit => exact ⟨_, _, rfl, Or.inl digit⟩
  | dotDigit digit => exact ⟨_, _, rfl, Or.inr rfl⟩

theorem number_starts (token : CPPNumber.Spells chars) : NumberStart chars := by
  induction token with
  | digit digit => exact .digit digit
  | dotDigit digit => exact .dotDigit digit
  | appendDigit token digit ih => exact ih.append _
  | appendNondigit token next ih => exact ih.append _
  | exponent token letter sign ih => exact ih.append _
  | dot token ih => exact ih.append _

theorem identifier_no_quote (token : CIdentifierToken.Spells chars) (quote : c ∈ ['"', '\'']) : c ∉ chars := by
  intro member
  have included := token.characters c member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at quote
  rcases quote with rfl | rfl <;> contradiction

private theorem encoding_word (member : encoding ∈ ["u8", "u", "U", "L"]) :
    CIdentifierToken.Spells encoding.toList := by
  apply CIdentifierToken.word_spells
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩

theorem encoded_starts (member : encoding ∈ ["u8", "u", "U", "L"]) (rest : List Char) :
    Starts IdentifierStart (encoding.toList ++ rest) :=
  (identifier_starts (encoding_word member)).append rest

/-- A consumed word cannot instead be the beginning of an encoded literal.
The proof compares both identifier candidates and uses the actual quote
continuation; it does not assume that a competitor came from our renderer. -/
theorem word_not_encoded (word : Consumes input (.word name) rest)
    (encoding : encoded ∈ ["u8", "u", "U", "L"]) (quote : marker ∈ ['"', '\''])
    (included : encoded.toList ++ marker :: tail <+: input) : False := by
  cases word with
  | word parts consumed safe =>
      obtain ⟨remaining, input_eq⟩ := included
      have inputShape : input = encoded.toList ++ marker :: (tail ++ remaining) := by
        simpa only [List.append_assoc, List.cons_append] using input_eq.symm
      have namePrefix : name.toList <+: input := ⟨rest, consumed.input_eq.symm⟩
      have encodedPrefix : encoded.toList <+: input := ⟨marker :: (tail ++ remaining), inputShape.symm⟩
      have nameBound : name.toList.length ≤ encoded.toList.length := by
        apply _root_.Parser.Scanner.prefix_before_delimiter (inputShape ▸ namePrefix)
        exact identifier_no_quote consumed.spelling quote
      have encodedBound := consumed.longest _ (encoding_word encoding) encodedPrefix
      have chars : name.toList = encoded.toList :=
        (List.prefix_of_prefix_length_le namePrefix encodedPrefix nameBound).eq_of_length_le encodedBound
      have names : name = encoded := String.toList_injective chars
      have restShape : rest = marker :: (tail ++ remaining) := by
        have same := consumed.input_eq.symm.trans inputShape
        simpa only [chars, List.append_cancel_left_eq] using same
      have forbidden := safe (names ▸ encoding) marker (tail ++ remaining) restShape
      simp only [List.mem_cons, List.not_mem_nil, or_false] at quote
      rcases quote with rfl | rfl
      · exact forbidden.1 rfl
      · exact forbidden.2 rfl

theorem NumberStart.not_identifier {first : Char} (start : NumberStart (first :: rest))
    (identifier : _root_.Parser.identStart first = true) : False := by
  cases start with
  | digit digit => simp [CLexical.identStart_not_digit identifier] at digit
  | dotDigit digit => contradiction

theorem word_not_number (word : Consumes input (.word name) rest)
    (candidate : CPPNumber.Spells chars) (included : chars <+: input) : False := by
  cases word with
  | word parts consumed safe =>
      obtain ⟨first, tail, nameChars, start, later⟩ := parts
      have number := (number_starts candidate).prefix included
      rw [consumed.input_eq, nameChars, List.cons_append] at number
      exact number.not_identifier start

theorem word_starts (word : Consumes input (.word name) rest) :
    Starts (fun c => _root_.Parser.identStart c = true) input := by
  cases word with
  | word parts consumed safe =>
      obtain ⟨first, tail, nameChars, start, later⟩ := parts
      rw [consumed.input_eq, nameChars]
      exact ⟨first, tail ++ rest, rfl, start⟩

theorem number_start_not_identifier (number : NumberStart input) (word : Starts IdentifierStart input) : False := by
  cases number with
  | digit digit => simp [word.head.not_digit] at digit
  | dotDigit digit =>
      have forbidden := word.head.character
      contradiction

theorem number_input_starts (number : Consumes input (.number spelling) rest) : NumberStart input := by
  cases number with
  | number spelled equal longest =>
      rw [equal]
      exact (number_starts spelled).append _

theorem quoted_starts (quoted : CString.Quoted chars) : Starts (fun c => c = '"') chars := by
  obtain ⟨body, rfl, valid⟩ := quoted
  exact ⟨'"', body ++ ['"'], rfl, rfl⟩

theorem string_input_starts (string : Consumes input (.string bytes) rest) : Starts (fun c => c = '"') input := by
  cases string with
  | string literal equal =>
      rw [equal]
      exact (quoted_starts (CString.denotes_quoted literal)).append _

end Rumoca.CTokens.Competition
