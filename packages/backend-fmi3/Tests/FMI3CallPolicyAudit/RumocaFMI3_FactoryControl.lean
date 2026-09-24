import RumocaFMI3.FactoryControl
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.FactoryControl.

#audit axioms Rumoca.FMI3.FactoryControl.Control.atomic_origin
#audit axioms Rumoca.FMI3.FactoryControl.Control.withHeap

-- Factory pointer migration: retained generic domains and actual typed routes.
#audit axioms Rumoca.FMI3.FactoryControl.Control
