import RumocaFMI3.TimeCalls
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.TimeCalls.

#audit axioms Rumoca.FMI3.TimeCalls.body_agrees
#audit axioms Rumoca.FMI3.TimeCalls.parameters_bound
#audit axioms Rumoca.FMI3.TimeCalls.bit_cases
#audit axioms Rumoca.FMI3.TimeCalls.query_cases
#audit axioms Rumoca.FMI3.TimeCalls.failure_unique
#audit axioms Rumoca.FMI3.TimeCalls.call_behaviors
#audit axioms Rumoca.FMI3.TimeCalls.null_behaviors
#audit axioms Rumoca.FMI3.TimeCalls.lifecycle_prefix
#audit axioms Rumoca.FMI3.TimeCalls.nonfinite_prefix
#audit axioms Rumoca.FMI3.TimeCalls.window_rejected_eval
#audit axioms Rumoca.FMI3.TimeCalls.failure_prefix
#audit axioms Rumoca.FMI3.TimeCalls.quiet_correct
#audit axioms Rumoca.FMI3.TimeCalls.suppressed_correct
#audit axioms Rumoca.FMI3.TimeCalls.logged_correct
#audit axioms Rumoca.FMI3.TimeCalls.admitted_finite
#audit axioms Rumoca.FMI3.TimeCalls.failure_excludes_success
