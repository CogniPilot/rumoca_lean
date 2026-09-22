import RumocaCore.GALEC.Elaboration.Assignments
import ProofAudit.Audit

-- Public authored roots and the retained source-address audit roots.
#audit axioms Rumoca.GALEC.Elaboration.Target.location
#audit axioms Rumoca.GALEC.Elaboration.TargetLowering.locating_correct
#audit axioms Rumoca.GALEC.Elaboration.AssignmentLowering.lower
#audit axioms Rumoca.GALEC.Elaboration.AssignmentLowering.Elaborates
#audit axioms Rumoca.GALEC.Elaboration.AssignmentLowering.lower_iff
#audit axioms Rumoca.GALEC.Elaboration.AssignmentLowering.Executes
#audit axioms Rumoca.GALEC.Elaboration.AssignmentLowering.lowering_correct
#audit axioms Rumoca.GALEC.Elaboration.AssignmentLowering.source_to_statement
