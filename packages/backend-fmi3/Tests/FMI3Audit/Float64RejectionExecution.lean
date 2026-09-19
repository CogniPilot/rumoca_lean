import RumocaFMI3.Float64RejectionExecution
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.Float64RejectionExecution.

#audit axioms Rumoca.FMI3.Float64Rejection.Request.behaves_iff
#audit axioms Rumoca.FMI3.Float64Rejection.Request.returned
#audit axioms Rumoca.FMI3.Float64Rejection.Returned.buffers
#audit axioms Rumoca.FMI3.Float64Rejection.Returned.recover
#audit axioms Rumoca.FMI3.Float64Rejection.Request.execution
#audit axioms Rumoca.FMI3.Float64Rejection.Returned.writable
