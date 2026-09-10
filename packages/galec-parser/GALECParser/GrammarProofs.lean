import GALECParser.Generated
import Parser.LALR.EBNF

open _root_.Parser

namespace Rumoca.GALEC.Generated

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- Concrete preprocessing binding: the current EBNF bytes process to the CFG
used by this parser. General EBNF metalanguage/desugaring preservation remains
open. Keep this computation in the parser, independent of compiler IR changes. -/
theorem grammar_processed :
    (LALR.Frontend.compile source).map (·.grammar) = .ok grammar := by decide +kernel

end Rumoca.GALEC.Generated
