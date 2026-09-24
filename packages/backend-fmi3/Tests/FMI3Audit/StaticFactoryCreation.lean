import RumocaFMI3.StaticFactoryCreation
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.StaticFactoryCreation.

#audit axioms Rumoca.FMI3.StaticFactory.create_silent
#audit axioms Rumoca.FMI3.StaticFactory.create_logged

-- Factory pointer migration: retained generic domains and actual typed routes.
#audit axioms Rumoca.FMI3.StaticFactory.create_logged_explicit
#audit axioms Rumoca.FMI3.StaticFactory.create_logged_with
#audit axioms Rumoca.FMI3.StaticFactory.create_silent_explicit
#audit axioms Rumoca.FMI3.StaticFactory.create_silent_with
