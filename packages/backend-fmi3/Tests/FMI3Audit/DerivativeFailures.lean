import RumocaFMI3.DerivativeFailures
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.DerivativeFailures.

#audit axioms Rumoca.FMI3.DerivativeCalls.query_cases
#audit axioms Rumoca.FMI3.DerivativeCalls.failure_unique
#audit axioms Rumoca.FMI3.DerivativeCalls.null_behaviors
#audit axioms Rumoca.FMI3.DerivativeCalls.invalid_run
#audit axioms Rumoca.FMI3.DerivativeCalls.failure_prefix
