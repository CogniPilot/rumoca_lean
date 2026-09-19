import Rumoca.FMI3Float64Rejection
import ProofAudit.Audit

-- Axiom audit for the roots defined in Rumoca.FMI3Float64Rejection.

#audit axioms Rumoca.FMI3.InitializationAccess.Recovery.completed_source
#audit axioms Rumoca.FMI3.Float64Rejection.Returned.source_recovery
#audit axioms Rumoca.FMI3.Float64Rejection.runtime_source
