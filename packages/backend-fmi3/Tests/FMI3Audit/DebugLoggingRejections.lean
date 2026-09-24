import RumocaFMI3.DebugLoggingRejections
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.DebugLoggingRejections.

-- Explicit-null migration: shared syntax, retained domains and typed execution.
#audit axioms Rumoca.FMI3.DebugLogging.iteration_invalid_behaviors_with
#audit axioms Rumoca.FMI3.DebugLogging.iteration_invalid_behaviors_explicit

#audit axioms Rumoca.FMI3.DebugLogging.suppressed_failure_contract
#audit axioms Rumoca.FMI3.DebugLogging.logged_failure_contract
#audit axioms Rumoca.FMI3.DebugLogging.iteration_invalid_behaviors
