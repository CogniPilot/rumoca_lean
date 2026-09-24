import GALECParser.Parser
import Parser.ScannerSpelling

/-! The GALEC scanner discharges the same generic source-location contract as
the Modelica frontend. No grammar or generated table is changed. -/
namespace Rumoca.GALEC.Syntax
open _root_.Parser

theorem scanner_preserves_text (word : String) : (scanner.classify word).text = word := by
  dsimp only [scanner]
  split <;> rfl

theorem scanner_preserves_numbers (spelling : String) : (scanner.number spelling).text = spelling :=
  rfl

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
