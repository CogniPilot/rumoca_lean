import RumocaFMI3.StaticFactoryExhaustion
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.StaticFactoryExhaustion.

#audit axioms Rumoca.FMI3.StaticFactory.exhaustion_path
#audit axioms Rumoca.FMI3.StaticFactory.exhausted_silent
#audit axioms Rumoca.FMI3.StaticFactory.exhausted_logged

-- Factory pointer migration: retained generic domains and actual typed routes.
#audit axioms Rumoca.FMI3.StaticFactory.exhausted_logged_explicit
#audit axioms Rumoca.FMI3.StaticFactory.exhausted_logged_with
#audit axioms Rumoca.FMI3.StaticFactory.exhausted_silent_explicit
#audit axioms Rumoca.FMI3.StaticFactory.exhausted_silent_with
#audit axioms Rumoca.FMI3.StaticFactory.exhaustion_path_with
