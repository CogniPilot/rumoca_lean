import ModelicaParser
import ModelicaParser.Annex
import ModelicaParser.Certificate
import ProofAudit.Audit

#audit axioms Rumoca.Generated.source_read_checked
#audit axioms Rumoca.Generated.source_notation_checked
#audit axioms Rumoca.Generated.lowering_checked
#audit axioms Rumoca.Generated.runtimeRules_eq
#audit axioms Rumoca.Generated.runtimeRules_productions
#audit axioms Rumoca.Generated.ebnf_correct
#audit axioms Rumoca.Generated.source_parse_correct
#audit axioms Rumoca.Generated.items_checked
#audit axioms Rumoca.Generated.safety_checked
#audit axioms Rumoca.Generated.budget_checked
#audit axioms Rumoca.Generated.progress_checked
#audit axioms Rumoca.Generated.parse_correct
#audit axioms Rumoca.Generated.parsed_tree
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

#audit axioms Rumoca.lex_correct
#audit axioms Rumoca.scan_sound
#audit axioms Rumoca.scan_complete
#audit axioms Rumoca.numberLength
#audit axioms Rumoca.numberLength_pos
#audit axioms Rumoca.stringLength
#audit axioms Rumoca.blockCommentLength
#audit axioms Rumoca.lineCommentLength
#audit axioms Rumoca.Lexes.ident_word
#audit axioms Rumoca.Lexes.ident_not_time
#audit axioms Rumoca.Lexes.spelled

#audit axioms Rumoca.Modelica.AST.leftAssociate
#audit axioms Rumoca.Modelica.Print.storedDefinition
#audit axioms Rumoca.Modelica.Print.expr_leftAssociate
#audit axioms Rumoca.Modelica.Structural.rules
#audit axioms Rumoca.Modelica.Structural.printResult
#audit axioms Rumoca.Modelica.Structural.covered
#audit axioms Rumoca.Modelica.Structural.licensed
#audit axioms Rumoca.Modelica.Structural.printed
#audit axioms Rumoca.Modelica.Structural.denotes_tokens
#audit axioms Rumoca.Modelica.Structural.storedDefinition_total
#audit axioms Rumoca.Modelica.Structural.storedDefinition_domain
#audit axioms Rumoca.Modelica.Structural.storedDefinition_correct
#audit axioms Rumoca.Modelica.StructureBridge.total
#audit axioms Rumoca.Modelica.StructureBridge.sound
#audit axioms Rumoca.Modelica.StructureBridge.source_accepts_iff
#audit axioms Rumoca.Modelica.StructureBridge.classifier_compatible
#audit axioms Rumoca.Modelica.StructureBridge.syntax_sound
#audit axioms Rumoca.Modelica.StructureBridge.parse_eq_build
#audit axioms Rumoca.Modelica.StructureBridge.build_total
#audit axioms Rumoca.Modelica.StructureBridge.build_sound
#audit axioms Rumoca.Modelica.StructureBridge.root_valid
#audit axioms Rumoca.Modelica.Structural.build_iff
#audit axioms Rumoca.Modelica.Structural.build_total
#audit axioms Rumoca.Modelica.Structural.build_sound
#audit axioms Rumoca.Modelica.Structural.parse_iff
#audit axioms Rumoca.Modelica.Structural.accepts_iff
#audit axioms Rumoca.Modelica.Structural.parse_printed
#audit axioms Rumoca.Modelica.Annex.arithmetic_expression_iff
#audit axioms Rumoca.Modelica.Annex.component_reference_iff

#audit axioms Rumoca.Modelica.isComment
#audit axioms Rumoca.Modelica.code
#audit axioms Rumoca.Modelica.code_uncommented
#audit axioms Rumoca.Modelica.parse
#audit axioms Rumoca.Modelica.Parsed.tokens
#audit axioms Rumoca.Modelica.parse_eq_parsed
#audit axioms Rumoca.Modelica.Parsed.printed
#audit axioms Rumoca.Modelica.Parsed.lexes
#audit axioms Rumoca.Modelica.Parsed.in_ebnf
#audit axioms Rumoca.Modelica.Parsed.unique
#audit axioms Rumoca.Modelica.accepts_iff
#audit axioms Rumoca.Modelica.located_lex_sound
#audit axioms Rumoca.Modelica.rejectedAt
#audit axioms Rumoca.Modelica.parseLocated
#audit axioms Rumoca.Modelica.codeLocations
#audit axioms Rumoca.Modelica.codeLocations_values
#audit axioms Rumoca.Modelica.locatedSpan
#audit axioms Rumoca.Modelica.LocatedParsed.erases
#audit axioms Rumoca.Modelica.LocatedParsed.codeLocations_erase
#audit axioms Rumoca.Modelica.LocatedParsed.lexemes
#audit axioms Rumoca.Modelica.LocatedParsed.disjoint
#audit axioms Rumoca.Modelica.LocatedParsed.tokenSpan_text
#audit axioms Rumoca.Modelica.Parsed.locations_exist
#audit axioms Rumoca.Modelica.Parsed.located_parsed
#audit axioms Rumoca.Modelica.Parsed.parseLocated_eq
#audit axioms Rumoca.Modelica.parseLocated_complete


#audit axioms Rumoca.Parallel.parse_eq_sequential
#audit axioms Rumoca.Parallel.parse_input_order
#audit axioms Rumoca.Parallel.Result.source_sound

#audit axioms Rumoca.Modelica.Certificate.token_tree
#audit axioms Rumoca.Modelica.Certificate.syntactic_of_certificates

namespace Rumoca.Modelica.CertificateCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/- Kernel regression of the certificate generator on a nested expression with
every operator, a call, a global reference and a parenthesized list. Admission
of these forms is static semantics. -/
certify_source nested "model Nested
  input Real u[2, n];
  output Real x(start = -1.5e3, each fixed = true) = .a.b[1];
equation
  der(x) = -f(u .* u, (g), true) + 2 * x / (3 - y);
  z = ();
end Nested;
"

#audit axioms nested.lexed
#audit axioms nested.checked
#audit axioms nested.structure_built
#audit axioms nested.denotes
#audit axioms nested.syntactic

/- Comments are lexemes with their own ranges; the grammar reads the code tokens. -/
certify_source commented "model M // line
  Real x; /* block */
equation der(x) = 1; end M;"

#audit axioms commented.lexed
#audit axioms commented.checked
#audit axioms commented.syntactic

end Rumoca.Modelica.CertificateCheck
