import RumocaFMI3.DebugLoggingBody
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.DebugLoggingBody.

-- Explicit-null migration: shared syntax, retained domains and typed execution.
#audit axioms Rumoca.FMI3.DebugLogging.prepare_code_with
#audit axioms Rumoca.FMI3.DebugLogging.prepare_code_explicit
#audit axioms Rumoca.FMI3.DebugLogging.code_success_behaviors_with
#audit axioms Rumoca.FMI3.DebugLogging.code_success_behaviors_explicit
#audit axioms Rumoca.FMI3.DebugLogging.code_unknown_behaviors_with
#audit axioms Rumoca.FMI3.DebugLogging.code_unknown_behaviors_explicit
#audit axioms Rumoca.FMI3.DebugLogging.code_missing_behaviors_with
#audit axioms Rumoca.FMI3.DebugLogging.code_missing_behaviors_explicit
#audit axioms Rumoca.FMI3.DebugLogging.code_behaviors_with
#audit axioms Rumoca.FMI3.DebugLogging.code_behaviors_explicit

#audit axioms Rumoca.FMI3.DebugLogging.prepare_code
#audit axioms Rumoca.FMI3.DebugLogging.Entries.readable
#audit axioms Rumoca.FMI3.DebugLogging.code_success_behaviors
#audit axioms Rumoca.FMI3.DebugLogging.code_unknown_behaviors
#audit axioms Rumoca.FMI3.DebugLogging.code_missing_behaviors
#audit axioms Rumoca.FMI3.DebugLogging.code_behaviors
