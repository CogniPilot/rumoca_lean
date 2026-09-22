import GALECParser
import GALECParser.GrammarProofs
import GALECParser.ScannerProofs
import GALECParser.StructuralParser
import GALECParser.SourceCompatibility
import GALECParser.DeclarationOrder
import ProofAudit.Audit

import GALECParser.LocatedCompleteness

#audit axioms Rumoca.GALEC.AST.Reference.unindexed

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
#audit axioms Rumoca.GALEC.Generated.runtimeRules_eq
#audit axioms Rumoca.GALEC.Generated.runtimeRules_productions
#audit axioms Rumoca.GALEC.Generated.ebnf_correct
#audit axioms Rumoca.GALEC.Generated.source_parse_correct

#audit axioms Rumoca.GALEC.Generated.located_fuel
#audit axioms Rumoca.GALEC.Generated.source_parseLocated_correct
#audit axioms Rumoca.GALEC.Generated.parseLocated_erases

#audit axioms Rumoca.GALEC.StructureBridge.total
#audit axioms Rumoca.GALEC.StructureBridge.sound
#audit axioms Rumoca.GALEC.StructureBridge.source_accepts_iff
#audit axioms Rumoca.GALEC.StructureBridge.classifier_compatible
#audit axioms Rumoca.GALEC.StructureBridge.syntax_sound
#audit axioms Rumoca.GALEC.StructureBridge.parse_eq_build
#audit axioms Rumoca.GALEC.StructureBridge.build_total
#audit axioms Rumoca.GALEC.StructureBridge.build_sound
#audit axioms Rumoca.GALEC.StructureBridge.root_valid
#audit axioms Rumoca.GALEC.Structural.build_iff
#audit axioms Rumoca.GALEC.Structural.build_total
#audit axioms Rumoca.GALEC.Structural.build_sound
#audit axioms Rumoca.GALEC.Structural.covered
#audit axioms Rumoca.GALEC.Structural.licensed
#audit axioms Rumoca.GALEC.Structural.program_total
#audit axioms Rumoca.GALEC.Structural.program_domain
#audit axioms Rumoca.GALEC.Structural.program_correct
#audit axioms Rumoca.GALEC.ProfileProjection.scalar_retraction
#audit axioms Rumoca.GALEC.ProfileProjection.tensor_retraction
#audit axioms Rumoca.GALEC.ProfileProjection.scalar_projection_exact
#audit axioms Rumoca.GALEC.ProfileProjection.tensor_projection_exact
#audit axioms Rumoca.GALEC.ProfileProjection.scalar_projection_iff
#audit axioms Rumoca.GALEC.ProfileProjection.tensor_projection_iff
#audit axioms Rumoca.GALEC.Syntax.Compatibility.scalar_reference_exact
#audit axioms Rumoca.GALEC.Syntax.Compatibility.tensor_reference_exact

#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.lookup_reference
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.lookup_product
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.lookup_startup
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.lookup_recalibrate
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.lookup_doStep
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.lookup_tensorDoStep
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.lookup_scalarBlock
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.lookup_tensorBlock
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.lookup_program
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.symbol_literal
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.terminal_words_literal
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.scalar_words_yield
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.scalar_words_ast
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.tensor_words_yield
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.tensor_words_ast
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.scalar_denotes_yield
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.tensor_denotes_yield
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.scalar_denotes_of_yield
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.tensor_denotes_of_yield
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.scalar_denotes_iff
#audit axioms Rumoca.GALEC.Structural.ProfileSemantics.tensor_denotes_iff
#audit axioms Rumoca.GALEC.Structural.buildScalar_tokens_iff
#audit axioms Rumoca.GALEC.Structural.buildTensor_tokens_iff
#audit axioms Rumoca.GALEC.Structural.buildScalar_eq_decode
#audit axioms Rumoca.GALEC.Structural.buildTensor_eq_decode

-- PA11: compositional runtime checks and their independent exact-image contracts.
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.identifier
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.one
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.two
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.three
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.four
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.empty
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.selfName
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.reference
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.literal
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.parens
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.binary
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.call
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.plusOne
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.product
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.derivativeCall
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.literalAssignment
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.scalarAssignment
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.productAssignment
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.callAssignment
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.methodBody
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.startup
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.recalibrate
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.scalarStep
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.tensorStep
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.declaration
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.scalarDeclarations
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.tensorDeclarations
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.toScalar
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.toTensor
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.identifier_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.one_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.two_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.three_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.four_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.empty_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.selfName_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.reference_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.literal_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.parens_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.binary_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.call_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.plusOne_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.product_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.derivativeCall_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.literalAssignment_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.scalarAssignment_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.productAssignment_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.callAssignment_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.methodBody_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.startup_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.recalibrate_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.scalarStep_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.tensorStep_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.declaration_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.scalarDeclarations_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.tensorDeclarations_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.scalar_projection_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.tensor_projection_iff
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.scalar_retraction
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.tensor_retraction
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.scalar_projection_exact
#audit axioms Rumoca.GALEC.ProfileProjection.Factors.tensor_projection_exact
#audit axioms Rumoca.GALEC.ProfileProjection.toScalar
#audit axioms Rumoca.GALEC.ProfileProjection.toTensor

#audit axioms Rumoca.GALEC.Syntax.DeclarationOrder.misplaced_position
#audit axioms Rumoca.GALEC.Syntax.DeclarationOrder.declared_name_position
#audit axioms Rumoca.GALEC.Syntax.DeclarationOrder.misplaced_not_tokens
#audit axioms Rumoca.GALEC.Syntax.DeclarationOrder.source_rejected
#audit axioms Rumoca.GALEC.Syntax.DeclarationOrder.source_rejected_at_position
