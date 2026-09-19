import RumocaFMI3.Float64Environment
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.Float64Environment.

#audit axioms Rumoca.FMI3.Float64Environment.body_agrees
#audit axioms Rumoca.FMI3.Float64Environment.helper_agrees
#audit axioms Rumoca.FMI3.Float64Environment.reaches
#audit axioms Rumoca.FMI3.Float64Environment.quiet_correct
#audit axioms Rumoca.FMI3.Float64Environment.failure_site
#audit axioms Rumoca.FMI3.Float64Environment.suppressed_correct
#audit axioms Rumoca.FMI3.Float64Environment.logged_correct
#audit axioms Rumoca.FMI3.Float64Environment.prepared_correct
