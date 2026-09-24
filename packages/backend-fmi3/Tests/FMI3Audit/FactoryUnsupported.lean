import RumocaFMI3.FactoryUnsupported
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.FactoryUnsupported.

#audit axioms Rumoca.FMI3.FactoryUnsupported.rejection_entry
#audit axioms Rumoca.FMI3.FactoryUnsupported.silent_behaviors
#audit axioms Rumoca.FMI3.FactoryUnsupported.logged_behaviors

-- Factory pointer migration: retained generic domains and actual typed routes.
#audit axioms Rumoca.FMI3.FactoryUnsupported.logged_behaviors_explicit
#audit axioms Rumoca.FMI3.FactoryUnsupported.logged_behaviors_with
#audit axioms Rumoca.FMI3.FactoryUnsupported.rejection_entry_with
#audit axioms Rumoca.FMI3.FactoryUnsupported.silent_behaviors_explicit
#audit axioms Rumoca.FMI3.FactoryUnsupported.silent_behaviors_with
