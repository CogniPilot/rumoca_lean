import RumocaFMI3.InitializationArguments
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.InitializationArguments.

#audit axioms Rumoca.FMI3.InitializationCalls.rejects_finite
#audit axioms Rumoca.FMI3.InitializationCalls.finite_admissible
#audit axioms Rumoca.FMI3.InitializationCalls.rejects_iff
#audit axioms Rumoca.FMI3.InitializationCalls.parameters_bound
#audit axioms Rumoca.FMI3.InitializationCalls.finite_parameters
#audit axioms Rumoca.FMI3.InitializationCalls.guard_eval
