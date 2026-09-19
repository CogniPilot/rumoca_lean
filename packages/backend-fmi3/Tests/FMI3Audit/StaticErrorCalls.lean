import RumocaFMI3.StaticErrorCalls
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.StaticErrorCalls.

#audit axioms Rumoca.FMI3.StaticErrors.helper_agrees
#audit axioms Rumoca.FMI3.StaticErrors.helper_parameters
#audit axioms Rumoca.FMI3.StaticErrors.dispatch_reaches
#audit axioms Rumoca.FMI3.StaticErrors.resume_reaches
#audit axioms Rumoca.FMI3.StaticErrors.helper_all_behaviors
#audit axioms Rumoca.FMI3.StaticErrors.helper_silent_behaviors
#audit axioms Rumoca.FMI3.StaticErrors.helper_silent_reaches
#audit axioms Rumoca.FMI3.StaticErrors.failure_prefix
#audit axioms Rumoca.FMI3.StaticErrors.statement_entry
#audit axioms Rumoca.FMI3.StaticErrors.failure_all_behaviors
#audit axioms Rumoca.FMI3.StaticErrors.failure_silent_behaviors
#audit axioms Rumoca.FMI3.StaticErrors.logging_cases
#audit axioms Rumoca.FMI3.StaticErrors.helper_suppressed_reaches
#audit axioms Rumoca.FMI3.StaticErrors.failure_suppressed_behaviors
#audit axioms Rumoca.FMI3.StaticErrors.statement_all_behaviors
#audit axioms Rumoca.FMI3.StaticErrors.statement_suppressed_behaviors
#audit axioms Rumoca.FMI3.StaticErrors.prefix_all_behaviors
#audit axioms Rumoca.FMI3.StaticErrors.prefix_suppressed_behaviors
#audit axioms Rumoca.FMI3.StaticErrors.path_suppressed_behaviors
#audit axioms Rumoca.FMI3.StaticErrors.path_all_behaviors
