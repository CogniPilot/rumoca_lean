import RumocaFMI3.InitializationErrors
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.InitializationErrors.

#audit axioms Rumoca.FMI3.InitializationCalls.failure_execution_correct
#audit axioms Rumoca.FMI3.InitializationCalls.silent_execution_correct
#audit axioms Rumoca.FMI3.InitializationCalls.time_guard
