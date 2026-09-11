import GALECParser.Syntax
import Parser.ScannerRefinement

/-! Scanner configuration proofs are separate from the EBNF computation so
lexical changes do not invalidate that larger cached certificate. -/
namespace Rumoca.GALEC.Syntax
open _root_.Parser

/-- The shared scanner's longer-symbol preference preserves every result of
the existing GALEC profile, including rejected inputs and diagnostic offsets. -/
theorem scanner_unchanged (source : String) :
    Scanner.lex scanner source = Scanner.StrictReference.lex scanner source := by
  apply Scanner.lex_disjoint
  intro c single
  by_cases colon : c = ':'
  · subst c
    simp [scanner] at single
  · simp [scanner, colon]

end Rumoca.GALEC.Syntax
