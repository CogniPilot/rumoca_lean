import RumocaFMI3.StaticFactoryInitialization
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.StaticFactoryInitialization.

#audit axioms Rumoca.FMI3.StaticFactory.select_step
#audit axioms Rumoca.FMI3.StaticFactory.guard_step
#audit axioms Rumoca.FMI3.StaticFactory.selected_bindings
#audit axioms Rumoca.FMI3.StaticFactory.initialization_reaches
#audit axioms Rumoca.FMI3.StaticFactory.guarded_initialization

-- Factory pointer migration: retained generic domains and actual typed routes.
#audit axioms Rumoca.FMI3.StaticFactory.code
#audit axioms Rumoca.FMI3.StaticFactory.codeWith
#audit axioms Rumoca.FMI3.StaticFactory.exhausted
#audit axioms Rumoca.FMI3.StaticFactory.exhaustedWith
#audit axioms Rumoca.FMI3.StaticFactory.function
#audit axioms Rumoca.FMI3.StaticFactory.functionWith
#audit axioms Rumoca.FMI3.StaticFactory.guard
#audit axioms Rumoca.FMI3.StaticFactory.guardWith
#audit axioms Rumoca.FMI3.StaticFactory.guard_step_with
#audit axioms Rumoca.FMI3.StaticFactory.guarded_initialization_with
#audit axioms Rumoca.FMI3.StaticFactory.logicalCode
#audit axioms Rumoca.FMI3.StaticFactory.logicalExhausted
#audit axioms Rumoca.FMI3.StaticFactory.logicalFunction
#audit axioms Rumoca.FMI3.StaticFactory.logicalGuard
