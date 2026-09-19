import RumocaFMI3.Float64Calls
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.Float64Calls.

#audit axioms Rumoca.FMI3.Float64Calls.getter_body
#audit axioms Rumoca.FMI3.Float64Calls.validation_closed
#audit axioms Rumoca.FMI3.Float64Calls.read_closed
#audit axioms Rumoca.FMI3.Float64Calls.parameters_bound
#audit axioms Rumoca.FMI3.Float64Calls.get_guard_run
#audit axioms Rumoca.FMI3.Float64Calls.reference_eval
#audit axioms Rumoca.FMI3.Float64Calls.validation_step
