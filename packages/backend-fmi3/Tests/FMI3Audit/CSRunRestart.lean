import RumocaFMI3.CSRunRestart
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.CSRunRestart.

#audit axioms Rumoca.FMI3.CSRun.restart_storage
#audit axioms Rumoca.FMI3.CSRun.restart_buffers
#audit axioms Rumoca.FMI3.CSRun.Stored.restart
#audit axioms Rumoca.FMI3.CSRun.Stored.framed
#audit axioms Rumoca.FMI3.CSRun.restart_atomic
#audit axioms Rumoca.FMI3.CSRun.advance_atomic
#audit axioms Rumoca.FMI3.CSRun.Stored.initialized
