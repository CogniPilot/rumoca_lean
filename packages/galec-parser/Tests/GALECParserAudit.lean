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
#audit axioms Rumoca.GALEC.Syntax.in_grammar
#audit axioms Rumoca.GALEC.Syntax.tree_complete
#audit axioms Rumoca.GALEC.Syntax.parse_complete

-- Tensor square profile: array declarations, elementwise product and Jacobian.
#audit axioms Rumoca.GALEC.Syntax.decodeTensor_tokens
#audit axioms Rumoca.GALEC.Syntax.tokens_of_decodeTensor
#audit axioms Rumoca.GALEC.Syntax.tensorUnit_resolved
#audit axioms Rumoca.GALEC.Syntax.in_grammar_tensor
#audit axioms Rumoca.GALEC.Syntax.tree_complete_tensor
#audit axioms Rumoca.GALEC.Syntax.parseTensor_complete
#audit axioms Rumoca.GALEC.Syntax.tensorScanner_preserves_text
#audit axioms Rumoca.GALEC.Syntax.tensorScanner_locations
#audit axioms Rumoca.GALEC.Syntax.TensorParsed.locations_exist
#audit axioms Rumoca.GALEC.Generated.safety_checked
#audit axioms Rumoca.GALEC.Generated.execution_safe
#audit axioms Rumoca.GALEC.Generated.first_checked
#audit axioms Rumoca.GALEC.Generated.nullable_coverage
#audit axioms Rumoca.GALEC.Generated.lookahead_coverage
#audit axioms Rumoca.GALEC.Generated.items_checked
#audit axioms Rumoca.GALEC.Generated.accepts_iff_parse
#audit axioms Rumoca.GALEC.Generated.budget_checked
#audit axioms Rumoca.GALEC.Generated.progress_checked
#audit axioms Rumoca.GALEC.Generated.fuel_eq
#audit axioms Rumoca.GALEC.Generated.accepts_iff_parse_bounded
#audit axioms Rumoca.GALEC.Generated.parse_terminates
#audit axioms Rumoca.GALEC.Generated.parse_correct
#audit axioms Rumoca.GALEC.Generated.parsed_tree

#audit axioms Rumoca.GALEC.Generated.source_read_checked
#audit axioms Rumoca.GALEC.Generated.source_notation_checked
#audit axioms Rumoca.GALEC.Generated.lowering_checked
#audit axioms Rumoca.GALEC.Generated.ebnf_correct
#audit axioms Rumoca.GALEC.Generated.source_parse_correct

#audit axioms Rumoca.GALEC.Generated.located_fuel
#audit axioms Rumoca.GALEC.Generated.source_parseLocated_correct
#audit axioms Rumoca.GALEC.Generated.parseLocated_erases
