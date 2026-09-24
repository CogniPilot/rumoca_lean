import RumocaFMI3.StaticFactoryReservation
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.StaticFactoryReservation.

#audit axioms Rumoca.FMI3.StaticFactory.reserve_entry
#audit axioms Rumoca.FMI3.StaticFactory.reserve_resume
#audit axioms Rumoca.FMI3.StaticFactory.successful

-- Factory pointer migration: retained generic domains and actual typed routes.
#audit axioms Rumoca.FMI3.StaticFactory.reserve_entry_with
#audit axioms Rumoca.FMI3.StaticFactory.reserve_resume_with
#audit axioms Rumoca.FMI3.StaticFactory.successful_with
