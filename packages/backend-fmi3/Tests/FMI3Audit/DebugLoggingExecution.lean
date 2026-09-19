import RumocaFMI3.DebugLoggingExecution
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.DebugLoggingExecution.

#audit axioms Rumoca.FMI3.DebugLogging.written_store
#audit axioms Rumoca.FMI3.DebugLogging.written_frame
#audit axioms Rumoca.FMI3.DebugLogging.written_storage
#audit axioms Rumoca.FMI3.DebugLogging.missing_step
#audit axioms Rumoca.FMI3.DebugLogging.declarations_reaches
#audit axioms Rumoca.FMI3.DebugLogging.write_logging_step
#audit axioms Rumoca.FMI3.DebugLogging.finish_reaches
