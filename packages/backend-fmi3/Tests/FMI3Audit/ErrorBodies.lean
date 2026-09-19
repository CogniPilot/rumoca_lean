import RumocaFMI3.ErrorBodies
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.ErrorBodies.

#audit axioms Rumoca.FMI3.ErrorBodies.failure_dispatch_run
#audit axioms Rumoca.FMI3.ErrorBodies.failure_log_arguments
#audit axioms Rumoca.FMI3.ErrorBodies.failure_silent_run
#audit axioms Rumoca.FMI3.ErrorBodies.failure_silent_correct
#audit axioms Rumoca.FMI3.ErrorBodies.nominals_reject_run
#audit axioms Rumoca.FMI3.ErrorBodies.nominals_reject_reaches
