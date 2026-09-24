import RumocaFMI3.FactoryRejectionControl
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.FactoryRejectionControl.

#audit axioms Rumoca.FMI3.FactoryRejection.Control.call_allowed
#audit axioms Rumoca.FMI3.FactoryRejection.Control.withHeap
#audit axioms Rumoca.FMI3.FactoryRejection.control_step

-- Factory pointer migration: retained generic domains and actual typed routes.
#audit axioms Rumoca.FMI3.FactoryRejection.Control
#audit axioms Rumoca.FMI3.FactoryRejection.ControlWith
#audit axioms Rumoca.FMI3.FactoryRejection.ControlWith.call_allowed
#audit axioms Rumoca.FMI3.FactoryRejection.ControlWith.withHeap
#audit axioms Rumoca.FMI3.FactoryRejection.ExplicitControl
#audit axioms Rumoca.FMI3.FactoryRejection.control_step_explicit
#audit axioms Rumoca.FMI3.FactoryRejection.control_step_with
