import ModelicaParser
import ModelicaParser.ActionsProofs
import ModelicaParser.Driven
import ModelicaParser.Array.Located
import ModelicaParser.Constant.Located
import ModelicaParser.ParserProofs
import ModelicaParser.LocatedProofs
import ModelicaParser.OriginProofs
import ModelicaParser.LocatedTotal
import ModelicaParser.ActionsLocatedTotal
import ProofAudit.Audit

#audit axioms Rumoca.Generated.source_read_checked
#audit axioms Rumoca.Generated.source_notation_checked
#audit axioms Rumoca.Generated.lowering_checked
#audit axioms Rumoca.Generated.ebnf_correct
#audit axioms Rumoca.Generated.source_parse_correct
#audit axioms Rumoca.Generated.items_checked
#audit axioms Rumoca.Generated.safety_checked
#audit axioms Rumoca.Generated.budget_checked
#audit axioms Rumoca.Generated.progress_checked
#audit axioms Rumoca.Generated.parse_correct
#audit axioms Rumoca.Generated.parsed_tree
#audit axioms Rumoca.parsed_tree
#audit axioms Rumoca.Grammar.unit_in_grammar
#audit axioms Rumoca.Driven.in_grammar
#audit axioms Rumoca.AST.decode_sound
#audit axioms Rumoca.lex_correct
#audit axioms Rumoca.parseTokens_sound
#audit axioms Rumoca.parseTokens_complete
#audit axioms Rumoca.parse_complete
#audit axioms Rumoca.parse_eq_parsed
#audit axioms Rumoca.parsed_source
#audit axioms Rumoca.parsed_in_ebnf
#audit axioms Rumoca.ParserActions.parseTokens_sound
#audit axioms Rumoca.ParserActions.parseTokens_complete
#audit axioms Rumoca.ParserActions.parse_complete
#audit axioms Rumoca.ParserActions.parsed_in_ebnf
#audit axioms Rumoca.Driven.decode_sound
#audit axioms Rumoca.Driven.resolve_complete
#audit axioms Rumoca.ArrayProfile.Call.jacobian_iff
#audit axioms Rumoca.ArrayProfile.decode_sound
#audit axioms Rumoca.ArrayProfile.decode_complete
#audit axioms Rumoca.ArrayProfile.in_grammar
#audit axioms Rumoca.ParserActions.LocatedParsed.erases
#audit axioms Rumoca.ParserActions.LocatedParsed.tokenSpan_text
#audit axioms Rumoca.ParserActions.LocatedParsed.disjoint
#audit axioms Rumoca.ArrayProfile.LocatedCall.arguments_contained
#audit axioms Rumoca.ArrayProfile.LocatedParsed.callLocation
#audit axioms Rumoca.ArrayProfile.LocatedParsed.resolve_complete
#audit axioms Rumoca.ParserActions.Parsed.locations_exist
#audit axioms Rumoca.ParserActions.Parsed.located_parsed
#audit axioms Rumoca.ParserActions.Parsed.parseLocated_eq
#audit axioms Rumoca.ParserActions.parseLocated_complete
#audit axioms Rumoca.located_lex_sound
#audit axioms Rumoca.LocatedParsed.erases
#audit axioms Rumoca.LocatedParsed.location_count
#audit axioms Rumoca.LocatedParsed.fieldSpan_eq_tokenSpan
#audit axioms Rumoca.LocatedParsed.state_field_text
#audit axioms Rumoca.Lexes.spelled
#audit axioms Rumoca.Parsed.locations_exist
#audit axioms Rumoca.Parsed.located_parsed
#audit axioms Rumoca.Parsed.parseLocated_eq
#audit axioms Rumoca.parseLocated_complete
#audit axioms Rumoca.LocatedParsed.lexemes
#audit axioms Rumoca.LocatedParsed.disjoint
#audit axioms Rumoca.Parallel.parse_eq_sequential
#audit axioms Rumoca.Parallel.parse_input_order
#audit axioms Rumoca.Parallel.Result.source_sound
#audit axioms Rumoca.LocatedParsed.tokenSpan_text
#audit axioms Rumoca.LocatedParsed.modelName_text
#audit axioms Rumoca.LocatedParsed.state_text
#audit axioms Rumoca.LocatedParsed.derivativeName_text
#audit axioms Rumoca.LocatedParsed.endName_text
#audit axioms Rumoca.LocatedParsed.resolved_references
#audit axioms Rumoca.LocatedParsed.resolve_complete
#audit axioms Rumoca.LocatedParsed.resolve_error_locations
#audit axioms Rumoca.LocatedParsed.field_range_contains
#audit axioms Rumoca.Origins.lookup
#audit axioms Rumoca.Origins.source_ancestry
#audit axioms Rumoca.Origins.leaf_text
#audit axioms Rumoca.Origins.production_ranges
#audit axioms Rumoca.Origins.production_boundaries
#audit axioms Rumoca.Generated.first_checked
#audit axioms Rumoca.Generated.execution_safe
#audit axioms Rumoca.Generated.nullable_coverage
#audit axioms Rumoca.Generated.lookahead_coverage
#audit axioms Rumoca.Generated.accepts_iff_parse
#audit axioms Rumoca.Generated.fuel_eq
#audit axioms Rumoca.Generated.accepts_iff_parse_bounded
#audit axioms Rumoca.Generated.parse_terminates
#audit axioms Rumoca.Generated.located_fuel
#audit axioms Rumoca.Generated.source_parseLocated_correct
#audit axioms Rumoca.Generated.parseLocated_erases

#audit axioms Rumoca.ConstantProfile.decode_sound
#audit axioms Rumoca.ConstantProfile.decode_complete
#audit axioms Rumoca.ConstantProfile.in_grammar
#audit axioms Rumoca.ConstantProfile.LocatedParsed.resolve_complete
