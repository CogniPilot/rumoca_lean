import RumocaFMI3.NominalFailures
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.NominalFailures.

#audit axioms Rumoca.FMI3.Nominals.reject_dispatch
#audit axioms Rumoca.FMI3.Nominals.reject_all_behaviors
#audit axioms Rumoca.FMI3.Nominals.reject_silent_behaviors
#audit axioms Rumoca.FMI3.Nominals.invalid_body
#audit axioms Rumoca.FMI3.Nominals.invalid_dispatch
#audit axioms Rumoca.FMI3.Nominals.invalid_all_behaviors
#audit axioms Rumoca.FMI3.Nominals.invalid_silent_behaviors
#audit axioms Rumoca.FMI3.Nominals.failure_message_collected
#audit axioms Rumoca.FMI3.Nominals.failure_all_behaviors
#audit axioms Rumoca.FMI3.Nominals.failure_silent_behaviors
#audit axioms Rumoca.FMI3.Nominals.query_cases
#audit axioms Rumoca.FMI3.Nominals.failure_cases_disjoint
