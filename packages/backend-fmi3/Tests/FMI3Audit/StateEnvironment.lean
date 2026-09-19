import RumocaFMI3.StateEnvironment
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.StateEnvironment.

#audit axioms Rumoca.FMI3.StateEnvironment.body_agrees
#audit axioms Rumoca.FMI3.StateEnvironment.quiet_correct
#audit axioms Rumoca.FMI3.StateEnvironment.suppressed_correct
#audit axioms Rumoca.FMI3.StateEnvironment.logged_correct
#audit axioms Rumoca.FMI3.StateEnvironment.prepared_correct
