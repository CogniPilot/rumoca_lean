import GALECParser.Parser
import Parser.ScannerSpelling

/-! The GALEC scanner discharges the same generic source-location contract as
the Modelica frontend, and never produces a `.*` token. -/
namespace Rumoca.GALEC.Syntax
open _root_.Parser

theorem scanner_preserves_text (word : String) : (scanner.classify word).text = word := by
  dsimp only [scanner]
  split <;> rfl

theorem scanner_preserves_numbers (spelling : String) : (scanner.number spelling).text = spelling :=
  rfl

private theorem spelling_ne (rest : List Char) (different : c ≠ '.') :
    String.ofList (c :: rest) ≠ ".*" := by
  intro same
  have listed := congrArg String.toList same
  rw [String.toList_ofList] at listed
  have pointwise : ".*".toList = ['.', '*'] := by decide
  rw [pointwise] at listed
  exact different (List.cons.inj listed).1

/-- `.*` is not a GALEC token: every word begins with a letter, every number with
a digit, every single symbol has one character and the only two-character
symbol is `:=`, so `.` and `*` always scan as two tokens. -/
theorem no_pointwise_token (lexed : Scanner.Lexes scanner cs tokens) :
    ∀ token ∈ tokens, token.text ≠ ".*" := by
  induction lexed with
  | nil => simp
  | space _ _ ih => exact ih
  | word _ start _ ih =>
    intro token member
    rcases List.mem_cons.mp member with rfl | member
    · rw [scanner_preserves_text]
      apply spelling_ne
      rintro rfl
      exact absurd start (by decide)
    · exact ih token member
  | number _ _ digit _ ih =>
    intro token member
    rcases List.mem_cons.mp member with rfl | member
    · rw [scanner_preserves_numbers]
      apply spelling_ne
      rintro rfl
      exact absurd digit (by decide)
    · exact ih token member
  | symbol _ _ _ lexed _ ih =>
    intro token member
    rcases List.mem_cons.mp member with rfl | member
    · cases lexed with
      | single _ _ =>
        intro same
        have listed : (String.singleton _).length = ".*".length := congrArg String.length same
        rw [String.length_singleton] at listed
        exact absurd listed (by decide)
      | pair paired =>
        apply spelling_ne
        rintro rfl
        simp [scanner] at paired
    · exact ih token member

/-- Every accepted GALEC lexical sequence receives exact UTF-8 locations. -/
theorem scanner_locations (source : String) (tokens : List Token)
    (accepted : Scanner.lex scanner source = .ok tokens) :
    ∃ xs, Source.attach scanner.space source.startPos tokens = some xs :=
  Scanner.lex_locations scanner scanner_preserves_text scanner_preserves_numbers
    source tokens accepted

/-- The actual scanned tokens of every successful parse receive locations. The
parse has no additional location-related rejection case. -/
theorem Parsed.locations_exist (parsed : Parsed source) :
    ∃ tokens xs, Scanner.lex scanner source = .ok tokens ∧
      Source.attach scanner.space source.startPos tokens = some xs := by
  obtain ⟨tokens, _, _, lexed, _⟩ := parsed.witnessed
  have accepted := (Scanner.lex_correct scanner source tokens).mpr lexed
  obtain ⟨xs, attached⟩ := scanner_locations source tokens accepted
  exact ⟨tokens, xs, accepted, attached⟩

end Rumoca.GALEC.Syntax
