import RumocaFMI3.InitializationAccess
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.InitializationAccess.

#audit axioms Rumoca.FMI3.InitializationAccess.start_allowed
#audit axioms Rumoca.FMI3.InitializationAccess.entry_storage
#audit axioms Rumoca.FMI3.InitializationAccess.entered_instance
#audit axioms Rumoca.FMI3.InitializationAccess.entered_buffers
#audit axioms Rumoca.FMI3.InitializationAccess.exited_instance
#audit axioms Rumoca.FMI3.InitializationAccess.exited_buffers
#audit axioms Rumoca.FMI3.InitializationAccess.initialization_history
#audit axioms Rumoca.FMI3.InitializationAccess.Certificate.executes
#audit axioms Rumoca.FMI3.InitializationAccess.Certificate.determines
#audit axioms Rumoca.FMI3.InitializationAccess.Certificate.execution_iff
