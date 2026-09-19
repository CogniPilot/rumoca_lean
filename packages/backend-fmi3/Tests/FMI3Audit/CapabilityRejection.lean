import RumocaFMI3.CapabilityRejection
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.CapabilityRejection.

#audit axioms Rumoca.FMI3.CapabilityRejection.locals_instance
#audit axioms Rumoca.FMI3.CapabilityRejection.arguments_exist
#audit axioms Rumoca.FMI3.CapabilityRejection.locals_fresh
#audit axioms Rumoca.FMI3.CapabilityRejection.parameters_bound
#audit axioms Rumoca.FMI3.CapabilityRejection.nonnull_body
#audit axioms Rumoca.FMI3.CapabilityRejection.failure_prefix
#audit axioms Rumoca.FMI3.CapabilityRejection.null_body
#audit axioms Rumoca.FMI3.CapabilityRejection.code_agrees
#audit axioms Rumoca.FMI3.CapabilityRejection.null_call
#audit axioms Rumoca.FMI3.CapabilityRejection.suppressed_call
#audit axioms Rumoca.FMI3.CapabilityRejection.logged_call
