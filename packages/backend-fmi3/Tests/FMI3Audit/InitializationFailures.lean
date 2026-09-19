import RumocaFMI3.InitializationFailures
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.InitializationFailures.

#audit axioms Rumoca.FMI3.InitializationCalls.query_cases
#audit axioms Rumoca.FMI3.InitializationCalls.failure_unique
#audit axioms Rumoca.FMI3.InitializationCalls.null_behaviors
#audit axioms Rumoca.FMI3.InitializationCalls.lifecycle_prefix
#audit axioms Rumoca.FMI3.InitializationCalls.arguments_prefix
#audit axioms Rumoca.FMI3.InitializationCalls.failure_prefix
