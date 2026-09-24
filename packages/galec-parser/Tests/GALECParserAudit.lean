import GALECParser
import GALECParser.GrammarProofs
import GALECParser.LocatedCompleteness
import GALECParser.Certificate
import GALECParser.Print
import ProofAudit.Audit

#audit axioms Rumoca.GALEC.AST.Reference.unindexed
#audit axioms Rumoca.GALEC.AST.Block.declarations

#audit axioms Rumoca.GALEC.Syntax.scanner_preserves_text
#audit axioms Rumoca.GALEC.Syntax.scanner_preserves_numbers
#audit axioms Rumoca.GALEC.Syntax.scanner_locations
#audit axioms Rumoca.GALEC.Syntax.Parsed.locations_exist
#audit axioms Rumoca.GALEC.Syntax.no_pointwise_token

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
#audit axioms Rumoca.GALEC.Structural.block_total
#audit axioms Rumoca.GALEC.Structural.block_domain
#audit axioms Rumoca.GALEC.Structural.block_correct
#audit axioms Rumoca.GALEC.Generated.grammar_processed
#audit axioms Rumoca.GALEC.Structural.loop_two_part
#audit axioms Rumoca.GALEC.Structural.loop_three_part
#audit axioms Rumoca.GALEC.Structural.parse_iff
#audit axioms Rumoca.GALEC.Structural.accepts_iff

#audit axioms Rumoca.GALEC.Syntax.Witness
#audit axioms Rumoca.GALEC.Syntax.Parsed
#audit axioms Rumoca.GALEC.Syntax.witnessed_build
#audit axioms Rumoca.GALEC.Syntax.parse
#audit axioms Rumoca.GALEC.Syntax.erase_parse
#audit axioms Rumoca.GALEC.Syntax.success_iff
#audit axioms Rumoca.GALEC.Syntax.lexical_error
#audit axioms Rumoca.GALEC.Syntax.witness_unique
#audit axioms Rumoca.GALEC.Syntax.accepts_iff
#audit axioms Rumoca.GALEC.Syntax.successful_tree

#audit axioms Rumoca.GALEC.Certificate.token_tree
#audit axioms Rumoca.GALEC.Certificate.witness_of_certificates
#audit axioms Rumoca.GALEC.Certificate.parse_of_certificates
#audit axioms Rumoca.GALEC.Print.block

namespace Rumoca.GALEC.CertificateCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/- Kernel regression of the certificate generator on the scalar layout. -/
certify_source unit "block UnitIntegrator
    output Real x;
protected
    constant Real samplePeriod;
public
    method Startup
    algorithm
        self.x := 0.0;
        self.samplePeriod := 1.0;
    end Startup;
    method Recalibrate
    algorithm
    end Recalibrate;
    method DoStep
    algorithm
        self.x := (self.x + 1.0);
    end DoStep;
end UnitIntegrator;
"

/-- The printer reproduces the certified text from its parsed tree. -/
theorem unit_printed : Print.block unit.ast = unit.source := by decide +kernel

#audit axioms unit.lexed
#audit axioms unit.checked
#audit axioms unit.structure_built
#audit axioms unit.denotes
#audit axioms unit.witness
#audit axioms unit.parsed
#audit axioms unit_printed

end Rumoca.GALEC.CertificateCheck
