import RumocaFMI3.Float64Failures
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.Float64Failures.

#audit axioms Rumoca.FMI3.Float64Calls.get_array_error_site
#audit axioms Rumoca.FMI3.Float64Calls.get_reference_error_site
#audit axioms Rumoca.FMI3.Float64Calls.query_cases
#audit axioms Rumoca.FMI3.Float64Calls.failure_unique
#audit axioms Rumoca.FMI3.Float64Calls.failure_site
