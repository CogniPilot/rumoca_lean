import ModelicaParser
import ModelicaParser.Annex
import ModelicaParser.Certificate
import ModelicaParser.Inversion
import ModelicaParser.Derivations
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
#audit axioms Rumoca.Modelica.Print.description
#audit axioms Rumoca.Modelica.Print.classAnnotation
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

#audit axioms Rumoca.Modelica.Good.storedDefinition
#audit axioms Rumoca.Modelica.Good.expr
#audit axioms Rumoca.Modelica.Good.name
#audit axioms Rumoca.Modelica.Good.typePrefix
#audit axioms Rumoca.Modelica.Good.declaration
#audit axioms Rumoca.Modelica.Good.declarations
#audit axioms Rumoca.Modelica.Good.componentClause
#audit axioms Rumoca.Modelica.Good.element
#audit axioms Rumoca.Modelica.Good.equation
#audit axioms Rumoca.Modelica.Good.equationSection
#audit axioms Rumoca.Modelica.Good.composition
#audit axioms Rumoca.Modelica.Good.classSpecifier
#audit axioms Rumoca.Modelica.Good.classDefinition
#audit axioms Rumoca.Modelica.Good.modification
#audit axioms Rumoca.Modelica.Good.strings
#audit axioms Rumoca.Modelica.Good.description
#audit axioms Rumoca.Modelica.Good.componentDeclaration
#audit axioms Rumoca.Modelica.Good.someEquation
#audit axioms Rumoca.Modelica.Good.invariant
#audit axioms Rumoca.Modelica.Good.exprs_iff
#audit axioms Rumoca.Modelica.Good.outputs_iff
#audit axioms Rumoca.Modelica.Good.components_iff
#audit axioms Rumoca.Modelica.Good.argumentList_iff
#audit axioms Rumoca.Modelica.Good.leftAssociate
#audit axioms Rumoca.Modelica.Good.literal_of_symbol
#audit axioms Rumoca.Modelica.Good.establishes
#audit axioms Rumoca.Modelica.Good.parse_good
#audit axioms Rumoca.Modelica.Good.ExpressionToken
#audit axioms Rumoca.Modelica.Good.ElementToken
#audit axioms Rumoca.Modelica.Good.BodyToken
#audit axioms Rumoca.Modelica.Good.expr_tokens
#audit axioms Rumoca.Modelica.Good.modification_tokens
#audit axioms Rumoca.Modelica.Good.name_tokens
#audit axioms Rumoca.Modelica.Good.descriptionString_tokens
#audit axioms Rumoca.Modelica.Good.annotationClause_tokens
#audit axioms Rumoca.Modelica.Good.description_tokens
#audit axioms Rumoca.Modelica.Good.componentDeclaration_tokens
#audit axioms Rumoca.Modelica.Good.someEquation_tokens
#audit axioms Rumoca.Modelica.Good.classAnnotation_tokens
#audit axioms Rumoca.Modelica.Good.declaration_tokens
#audit axioms Rumoca.Modelica.Good.element_tokens
#audit axioms Rumoca.Modelica.Good.equation_tokens
#audit axioms Rumoca.Modelica.Good.elements_tokens
#audit axioms Rumoca.Modelica.Good.equations_tokens
#audit axioms Rumoca.Modelica.Good.composition_tokens
#audit axioms Rumoca.Modelica.Good.not_mem_of_tokens
#audit axioms Rumoca.Modelica.Good.split_unique
#audit axioms Rumoca.Modelica.Good.not_named_literal
#audit axioms Rumoca.Modelica.Good.component_ne_nil
#audit axioms Rumoca.Modelica.Good.reference_ne_nil
#audit axioms Rumoca.Modelica.Good.expr_ne_nil
#audit axioms Rumoca.Modelica.Good.callee_ne_nil
#audit axioms Rumoca.Modelica.Good.reference_head
#audit axioms Rumoca.Modelica.Good.bare_of_printed
#audit axioms Rumoca.Modelica.Good.signed_of_printed
#audit axioms Rumoca.Modelica.Good.derivative_of_printed
#audit axioms Rumoca.Modelica.Good.subscripts_nil
#audit axioms Rumoca.Modelica.Good.optionalModification_nil
#audit axioms Rumoca.Modelica.Good.condition_nil
#audit axioms Rumoca.Modelica.Good.description_nil
#audit axioms Rumoca.Modelica.Good.Plain
#audit axioms Rumoca.Modelica.Good.description_plain
#audit axioms Rumoca.Modelica.Good.element_of_printed
#audit axioms Rumoca.Modelica.Good.not_expression_equals
#audit axioms Rumoca.Modelica.Good.equation_of_printed
#audit axioms Rumoca.Modelica.Good.composition_of_printed
#audit axioms Rumoca.Modelica.Good.storedDefinition_of_printed
#audit axioms Rumoca.Modelica.Derivations.many
#audit axioms Rumoca.Modelica.Derivations.componentReference_ident
#audit axioms Rumoca.Modelica.Derivations.expression_of_arithmetic
#audit axioms Rumoca.Modelica.Derivations.simpleExpression_of_arithmetic
#audit axioms Rumoca.Modelica.Derivations.term_of_primary
#audit axioms Rumoca.Modelica.Derivations.arithmetic_of_term
#audit axioms Rumoca.Modelica.Derivations.arithmetic_signed
#audit axioms Rumoca.Modelica.Derivations.primary_ident
#audit axioms Rumoca.Modelica.Derivations.arithmetic_ident
#audit axioms Rumoca.Modelica.Derivations.primary_derivative
#audit axioms Rumoca.Modelica.Derivations.descriptionString_empty
#audit axioms Rumoca.Modelica.Derivations.description_empty
#audit axioms Rumoca.Modelica.Derivations.someEquation
#audit axioms Rumoca.Modelica.Derivations.element_declaration
#audit axioms Rumoca.Modelica.Derivations.composition
#audit axioms Rumoca.Modelica.Derivations.accepts_model
#audit axioms Rumoca.StringBody
#audit axioms Rumoca.stringLength_body
#audit axioms Rumoca.stringLength_sound
#audit axioms Rumoca.string_maximal
#audit axioms Rumoca.comment_not_nested
#audit axioms Rumoca.quoted_identifier_rejected

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

/- Description strings, annotations with nested class modifications and
condition attributes parse in full; admission is static semantics. -/
certify_source described "model Described \"a\" + \"b\"
  Real x(start = 1 \"s\") \"state\" annotation(Dialog(group = g, enable = true));
  Real y if c \"conditional\";
equation
  der(x) = y \"rate\" annotation(HideResult = true);
  annotation(Icon(coordinateSystem(preserveAspectRatio = true)), defaultComponentName = c);
end Described;
"

#audit axioms described.lexed
#audit axioms described.checked
#audit axioms described.syntactic

end Rumoca.Modelica.CertificateCheck
