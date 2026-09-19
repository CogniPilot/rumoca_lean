import RumocaFMI3.StaticFactoryInitialization
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.StaticFactoryInitialization.

#audit axioms Rumoca.FMI3.StaticFactory.select_step
#audit axioms Rumoca.FMI3.StaticFactory.guard_step
#audit axioms Rumoca.FMI3.StaticFactory.selected_bindings
#audit axioms Rumoca.FMI3.StaticFactory.initialization_reaches
#audit axioms Rumoca.FMI3.StaticFactory.guarded_initialization
