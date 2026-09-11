import GALECParser
import GALECParser.GrammarProofs
import GALECParser.ScannerProofs
import ProofAudit.Audit
import GALECParser.LocatedCompleteness

#audit axioms Rumoca.GALEC.Syntax.scanner_preserves_text
#audit axioms Rumoca.GALEC.Syntax.scanner_locations
#audit axioms Rumoca.GALEC.Syntax.Parsed.locations_exist

#audit axioms Rumoca.GALEC.Syntax.decode_tokens
#audit axioms Rumoca.GALEC.Syntax.scanner_unchanged
#audit axioms Rumoca.GALEC.Syntax.tokens_of_decode
#audit axioms Rumoca.GALEC.Syntax.unit_tree_checked
#audit axioms Rumoca.GALEC.Syntax.tree_complete
#audit axioms Rumoca.GALEC.Syntax.parse_complete
#audit axioms Rumoca.GALEC.Generated.safety_checked
#audit axioms Rumoca.GALEC.Generated.execution_safe
#audit axioms Rumoca.GALEC.Generated.first_checked
#audit axioms Rumoca.GALEC.Generated.nullable_coverage
#audit axioms Rumoca.GALEC.Generated.lookahead_coverage
