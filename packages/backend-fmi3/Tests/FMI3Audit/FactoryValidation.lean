import RumocaFMI3.FactoryValidation
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.FactoryValidation.

#audit axioms Rumoca.FMI3.FactoryValidation.admission_equivalence
#audit axioms Rumoca.FMI3.FactoryValidation.rejected_silent
#audit axioms Rumoca.FMI3.FactoryValidation.rejected_logged

-- Factory pointer migration: retained generic domains and actual typed routes.
#audit axioms Rumoca.FMI3.FactoryValidation.admission_equivalence_with
#audit axioms Rumoca.FMI3.FactoryValidation.logicalRemaining
#audit axioms Rumoca.FMI3.FactoryValidation.rejected_logged_with
#audit axioms Rumoca.FMI3.FactoryValidation.rejected_silent_with
#audit axioms Rumoca.FMI3.FactoryValidation.remaining
#audit axioms Rumoca.FMI3.FactoryValidation.remainingWith
