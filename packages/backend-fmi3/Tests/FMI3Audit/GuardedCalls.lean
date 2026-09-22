import RumocaFMI3.GuardedCalls
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.GuardedCalls.

#audit axioms Rumoca.FMI3.GuardedCalls.rejected_prefix
#audit axioms Rumoca.FMI3.GuardedCalls.rejected_all_behaviors
#audit axioms Rumoca.FMI3.GuardedCalls.rejected_silent_behaviors
#audit axioms Rumoca.FMI3.GuardedCalls.rejected_missing_behaviors
#audit axioms Rumoca.FMI3.GuardedCalls.null_body
#audit axioms Rumoca.FMI3.GuardedCalls.null_behaviors
#audit axioms Rumoca.FMI3.GuardedCalls.FailurePrefix.all_behaviors
#audit axioms Rumoca.FMI3.GuardedCalls.FailurePrefix.silent_behaviors

#audit axioms Rumoca.FMI3.GuardedCalls.FailurePrefix.readonly
#audit axioms Rumoca.FMI3.GuardedCalls.FailurePrefix.error_readonly
