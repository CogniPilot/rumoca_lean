import RumocaFMI3.Float64RejectionMemory
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.Float64RejectionMemory.

#audit axioms Rumoca.FMI3.Float64Access.Instance.failed
#audit axioms Rumoca.FMI3.Float64Access.Instance.record_preserved
#audit axioms Rumoca.FMI3.Float64Rejection.Frame.record
#audit axioms Rumoca.FMI3.Float64Rejection.Frame.owners
#audit axioms Rumoca.FMI3.Float64Rejection.Frame.writable
