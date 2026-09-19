import RumocaFMI3.CountEnvironment
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.CountEnvironment.

#audit axioms Rumoca.FMI3.CountEnvironment.body_agrees
#audit axioms Rumoca.FMI3.CountEnvironment.quiet_correct
#audit axioms Rumoca.FMI3.CountEnvironment.QuietContract.returned
#audit axioms Rumoca.FMI3.CountEnvironment.suppressed_correct
#audit axioms Rumoca.FMI3.CountEnvironment.logged_correct
#audit axioms Rumoca.FMI3.CountEnvironment.prepared_correct
