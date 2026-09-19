import RumocaFMI3.Termination
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.Termination.

#audit axioms Rumoca.FMI3.Termination.body
#audit axioms Rumoca.FMI3.Termination.closed
#audit axioms Rumoca.FMI3.Termination.body_agrees
#audit axioms Rumoca.FMI3.Termination.call_behaviors
#audit axioms Rumoca.FMI3.Termination.null_behaviors
#audit axioms Rumoca.FMI3.Termination.failure_prefix
#audit axioms Rumoca.FMI3.Termination.quiet_correct
#audit axioms Rumoca.FMI3.Termination.suppressed_correct
#audit axioms Rumoca.FMI3.Termination.logged_correct
