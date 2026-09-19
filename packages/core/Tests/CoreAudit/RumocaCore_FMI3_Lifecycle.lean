import RumocaCore.FMI3.Lifecycle
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaCore.FMI3.Lifecycle.

#audit axioms Rumoca.FMI3.allowed_correct
#audit axioms Rumoca.FMI3.nominals_reject_instantiated
#audit axioms Rumoca.FMI3.counts_reject_computation_and_termination
#audit axioms Rumoca.FMI3.invalid_call_error
#audit axioms Rumoca.FMI3.invalid_call_final_values
#audit axioms Rumoca.FMI3.terminated_me_queries
#audit axioms Rumoca.FMI3.reset_recovers
#audit axioms Rumoca.FMI3.me_initialization
#audit axioms Rumoca.FMI3.cs_initialization
#audit axioms Rumoca.FMI3.cs_cannot_use_me_set_time
#audit axioms Rumoca.FMI3.evaluation_allowed_iff
#audit axioms Rumoca.FMI3.evaluation_rejects_initialization
#audit axioms Rumoca.FMI3.variable_setter_allowed_iff
#audit axioms Rumoca.FMI3.variable_setter_terminated
#audit axioms Rumoca.FMI3.state_assignment_endpoint
#audit axioms Rumoca.FMI3.cs_empty_setter_endpoint
