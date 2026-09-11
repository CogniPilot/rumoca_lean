import GALECParser.Parser
import Parser.ScannerSpelling

/-! The GALEC scanner discharges the same generic source-location contract as
the Modelica frontend. No grammar or generated table is changed. -/
namespace Rumoca.GALEC.Syntax
open _root_.Parser

theorem scanner_preserves_text (word : String) : (scanner.classify word).text = word := by
  dsimp only [scanner]
  split <;> rfl

/-- Every accepted GALEC lexical sequence receives exact UTF-8 locations. -/
theorem scanner_locations (source : String) (tokens : List Token)
    (accepted : Scanner.lex scanner source = .ok tokens) :
    ∃ xs, Source.attach scanner.space source.startPos tokens = some xs :=
  Scanner.lex_locations scanner scanner_preserves_text source tokens accepted

/-- The independently checked GALEC parse supplies all premises of attachment
completeness. Its source has no additional location-related rejection case. -/
theorem Parsed.locations_exist (parsed : Parsed source) :
    ∃ xs, Source.attach scanner.space source.startPos parsed.ast.tokens = some xs :=
  scanner_locations source parsed.ast.tokens ((Scanner.lex_correct scanner source _).mpr parsed.lexical)

end Rumoca.GALEC.Syntax
