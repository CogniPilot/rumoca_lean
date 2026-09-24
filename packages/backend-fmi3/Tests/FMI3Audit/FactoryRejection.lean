import RumocaFMI3.FactoryRejection
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.FactoryRejection.

#audit axioms Rumoca.FMI3.FactoryRejection.identity_guard
#audit axioms Rumoca.FMI3.FactoryRejection.dispatch
#audit axioms Rumoca.FMI3.FactoryRejection.return_null
#audit axioms Rumoca.FMI3.FactoryRejection.callback_entry
#audit axioms Rumoca.FMI3.FactoryRejection.silent_equivalence
#audit axioms Rumoca.FMI3.FactoryRejection.all_behaviors

-- Factory pointer migration: retained generic domains and actual typed routes.
#audit axioms Rumoca.FMI3.FactoryRejection.PointerPresentLaw
#audit axioms Rumoca.FMI3.FactoryRejection.all_behaviors_explicit
#audit axioms Rumoca.FMI3.FactoryRejection.all_behaviors_with
#audit axioms Rumoca.FMI3.FactoryRejection.code
#audit axioms Rumoca.FMI3.FactoryRejection.codeWith
#audit axioms Rumoca.FMI3.FactoryRejection.dispatch_explicit
#audit axioms Rumoca.FMI3.FactoryRejection.dispatch_with
#audit axioms Rumoca.FMI3.FactoryRejection.explicitPresent
#audit axioms Rumoca.FMI3.FactoryRejection.explicit_present_law
#audit axioms Rumoca.FMI3.FactoryRejection.identity_guard_with
#audit axioms Rumoca.FMI3.FactoryRejection.logicalCode
#audit axioms Rumoca.FMI3.FactoryRejection.logical_present_law
#audit axioms Rumoca.FMI3.FactoryRejection.silent_equivalence_explicit
#audit axioms Rumoca.FMI3.FactoryRejection.silent_equivalence_with
