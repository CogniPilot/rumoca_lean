import RumocaCore.Modelica.Unit
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaCore.Modelica.Unit.

#audit axioms Rumoca.AST.resolve
#audit axioms Rumoca.AST.resolve_complete
#audit axioms Rumoca.AST.select
#audit axioms Rumoca.AST.select_printed
#audit axioms Rumoca.AST.selection
#audit axioms Rumoca.parse
#audit axioms Rumoca.parseLocated
#audit axioms Rumoca.parse_eq_parsed
#audit axioms Rumoca.parsed_lexes
#audit axioms Rumoca.parsed_in_ebnf
#audit axioms Rumoca.Parsed.tokens_eq
#audit axioms Rumoca.Parsed.located_parsed
#audit axioms Rumoca.Parsed.parseLocated_eq
#audit axioms Rumoca.LocatedParsed.location_count
#audit axioms Rumoca.LocatedParsed.resolve
#audit axioms Rumoca.LocatedParsed.erases
#audit axioms Rumoca.LocatedParsed.fieldSpan_eq_tokenSpan
#audit axioms Rumoca.LocatedParsed.modelName_text
#audit axioms Rumoca.LocatedParsed.state_text
#audit axioms Rumoca.LocatedParsed.state_field_text
#audit axioms Rumoca.LocatedParsed.derivativeName_text
#audit axioms Rumoca.LocatedParsed.endName_text
#audit axioms Rumoca.LocatedParsed.constant_text
#audit axioms Rumoca.LocatedParsed.resolved_references
#audit axioms Rumoca.LocatedParsed.resolve_complete
#audit axioms Rumoca.LocatedParsed.resolve_error_locations
#audit axioms Rumoca.AST.Model.names
#audit axioms Rumoca.AST.Model.Admissible
#audit axioms Rumoca.AST.sourceFamily.syntactic
#audit axioms Rumoca.AST.select_complete
#audit axioms Rumoca.AST.parse_complete
