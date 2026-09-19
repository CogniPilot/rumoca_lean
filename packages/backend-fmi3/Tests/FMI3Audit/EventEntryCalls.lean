import RumocaFMI3.EventEntryCalls
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.EventEntryCalls.

#audit axioms Rumoca.FMI3.EventEntry.allowed
#audit axioms Rumoca.FMI3.EventEntry.body
#audit axioms Rumoca.FMI3.EventEntry.body_agrees
#audit axioms Rumoca.FMI3.EventEntry.call_behaviors
#audit axioms Rumoca.FMI3.EventEntry.continuous_run
#audit axioms Rumoca.FMI3.EventEntry.failure_prefix
#audit axioms Rumoca.FMI3.EventEntry.logged_correct
#audit axioms Rumoca.FMI3.EventEntry.null_behaviors
#audit axioms Rumoca.FMI3.EventEntry.query_cases
#audit axioms Rumoca.FMI3.EventEntry.quiet_correct
#audit axioms Rumoca.FMI3.EventEntry.suppressed_correct
