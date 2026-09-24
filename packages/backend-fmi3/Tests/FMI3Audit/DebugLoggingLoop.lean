import RumocaFMI3.DebugLoggingLoop
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.DebugLoggingLoop.

-- Explicit-null migration: shared syntax, retained domains and typed execution.
#audit axioms Rumoca.FMI3.DebugLogging.validation_prefix_equivalence_with
#audit axioms Rumoca.FMI3.DebugLogging.validation_prefix_equivalence_explicit
#audit axioms Rumoca.FMI3.DebugLogging.validation_valid_equivalence_with
#audit axioms Rumoca.FMI3.DebugLogging.validation_valid_equivalence_explicit

#audit axioms Rumoca.FMI3.DebugLogging.entry_eval
#audit axioms Rumoca.FMI3.DebugLogging.validation_prefix_equivalence
#audit axioms Rumoca.FMI3.DebugLogging.validation_valid_equivalence
