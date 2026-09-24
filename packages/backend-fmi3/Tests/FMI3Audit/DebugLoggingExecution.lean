import RumocaFMI3.DebugLoggingExecution
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.DebugLoggingExecution.

-- Explicit-null migration: shared syntax, retained domains and typed execution.
#audit axioms Rumoca.FMI3.DebugLogging.missing_step_with
#audit axioms Rumoca.FMI3.DebugLogging.missing_step_explicit
#audit axioms Rumoca.FMI3.DebugLogging.missing_zero_step

#audit axioms Rumoca.FMI3.DebugLogging.written_store
#audit axioms Rumoca.FMI3.DebugLogging.written_frame
#audit axioms Rumoca.FMI3.DebugLogging.written_storage
#audit axioms Rumoca.FMI3.DebugLogging.missing_step
#audit axioms Rumoca.FMI3.DebugLogging.declarations_reaches
#audit axioms Rumoca.FMI3.DebugLogging.write_logging_step
#audit axioms Rumoca.FMI3.DebugLogging.finish_reaches

#audit axioms Rumoca.FMI3.DebugLogging.missingWithConditions
#audit axioms Rumoca.FMI3.DebugLogging.codeWithConditions
#audit axioms Rumoca.FMI3.DebugLogging.rawCountMissing
#audit axioms Rumoca.FMI3.DebugLogging.rawCountCode
#audit axioms Rumoca.FMI3.DebugLogging.missing_count_next
#audit axioms Rumoca.FMI3.DebugLogging.missing_step_count
#audit axioms Rumoca.FMI3.DebugLogging.missing_step_typed
#audit axioms Rumoca.FMI3.DebugLogging.missing_zero_step_typed
#audit axioms Rumoca.FMI3.DebugLogging.code_count_behaviors
