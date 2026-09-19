import RumocaFMI3.StateEntry
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.StateEntry.

#audit axioms Rumoca.FMI3.StateCalls.Entry.parameters_bound
#audit axioms Rumoca.FMI3.StateCalls.Entry.parameters_valid
#audit axioms Rumoca.FMI3.StateCalls.Entry.body_eq
#audit axioms Rumoca.FMI3.StateCalls.Entry.null_behaviors
#audit axioms Rumoca.FMI3.StateCalls.Entry.rejected_all_behaviors
#audit axioms Rumoca.FMI3.StateCalls.Entry.rejected_silent_behaviors
#audit axioms Rumoca.FMI3.StateCalls.Entry.invalid_run
#audit axioms Rumoca.FMI3.StateCalls.Entry.invalid_prefix
#audit axioms Rumoca.FMI3.StateCalls.Entry.nonfinite_run
#audit axioms Rumoca.FMI3.StateCalls.Entry.nonfinite_prefix
#audit axioms Rumoca.FMI3.StateCalls.Entry.query_cases
#audit axioms Rumoca.FMI3.StateCalls.Entry.failure_unique
#audit axioms Rumoca.FMI3.StateCalls.Entry.failure_prefix
