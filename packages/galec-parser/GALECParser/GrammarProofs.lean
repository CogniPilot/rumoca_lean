import GALECParser.Generated
import Parser.LALR.EBNF

open _root_.Parser

namespace Rumoca.GALEC.Generated

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- Concrete preprocessing binding: the current EBNF bytes process to the CFG
used by this parser. Reuse the emitted reader certificate; generic expression
preservation is supplied separately by `ebnf_correct`. The independent EBNF
metalanguage-reader proof remains open. -/
theorem grammar_processed :
    (LALR.Frontend.compile source).map (·.grammar) = .ok grammar := by
  rw [LALR.Frontend.compile_of_parse source_read_checked]
  decide +kernel

end Rumoca.GALEC.Generated
