import RumocaCore.GALEC.Elaboration.Reads
import ProofAudit.Audit

-- Public authored roots and the retained source-address audit roots.
#audit axioms Rumoca.GALEC.Elaboration.Read
#audit axioms Rumoca.GALEC.Elaboration.Read.term
#audit axioms Rumoca.GALEC.Elaboration.Read.value
#audit axioms Rumoca.GALEC.Elaboration.Read.term_evaluates
#audit axioms Rumoca.GALEC.Elaboration.ReadLowering.lower
#audit axioms Rumoca.GALEC.Elaboration.ReadLowering.Elaborates
#audit axioms Rumoca.GALEC.Elaboration.ReadLowering.lower_iff
#audit axioms Rumoca.GALEC.Elaboration.ReadLowering.Evaluates
#audit axioms Rumoca.GALEC.Elaboration.ReadLowering.lowering_sound
#audit axioms Rumoca.GALEC.Elaboration.ReadLowering.evaluates_unique
#audit axioms Rumoca.GALEC.Elaboration.ReadLowering.lowering_correct
#audit axioms Rumoca.GALEC.Elaboration.ReadLowering.source_to_term
