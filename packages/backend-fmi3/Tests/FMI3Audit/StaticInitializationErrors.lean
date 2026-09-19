import RumocaFMI3.StaticInitializationErrors
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.StaticInitializationErrors.

#audit axioms Rumoca.FMI3.StaticInitialization.enter_silent_correct
#audit axioms Rumoca.FMI3.StaticInitialization.enter_logged_correct
#audit axioms Rumoca.FMI3.StaticInitialization.exit_silent_correct
#audit axioms Rumoca.FMI3.StaticInitialization.exit_logged_correct
#audit axioms Rumoca.FMI3.StaticInitialization.prepared_correct
#audit axioms Rumoca.FMI3.StaticInitialization.enter_suppressed_correct
#audit axioms Rumoca.FMI3.StaticInitialization.exit_suppressed_correct
