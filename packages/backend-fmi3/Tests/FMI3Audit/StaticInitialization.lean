import RumocaFMI3.StaticInitialization
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.StaticInitialization.

#audit axioms Rumoca.FMI3.StaticInitialization.interface_types
#audit axioms Rumoca.FMI3.StaticInitialization.enter_agrees
#audit axioms Rumoca.FMI3.StaticInitialization.exit_agrees
#audit axioms Rumoca.FMI3.StaticInitialization.entry_storage
#audit axioms Rumoca.FMI3.StaticInitialization.enter_call
#audit axioms Rumoca.FMI3.StaticInitialization.exit_call
#audit axioms Rumoca.FMI3.StaticInitialization.null_call
#audit axioms Rumoca.FMI3.StaticInitialization.quiet_correct
#audit axioms Rumoca.FMI3.StaticInitialization.exited_metadata
#audit axioms Rumoca.FMI3.StaticInitialization.exited_owners
