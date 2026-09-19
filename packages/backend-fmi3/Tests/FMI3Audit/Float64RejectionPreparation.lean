import RumocaFMI3.Float64RejectionPreparation
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.Float64RejectionPreparation.

#audit axioms Rumoca.FMI3.Float64Rejection.input_run
#audit axioms Rumoca.FMI3.Float64Rejection.input_read
#audit axioms Rumoca.FMI3.Float64Rejection.Request.prepare_frame
#audit axioms Rumoca.FMI3.Float64Rejection.Request.prepare_correct
#audit axioms Rumoca.FMI3.Float64Rejection.Request.prepared_instance
