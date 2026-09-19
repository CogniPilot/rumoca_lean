import RumocaC.CallIntervalTrace
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.CallIntervalTrace.

#audit axioms Rumoca.CCalls.Concurrent.interval_erases
#audit axioms Rumoca.CCalls.Concurrent.ownTrace_append
#audit axioms Rumoca.CCalls.Concurrent.silent_interval_history
#audit axioms Rumoca.CCalls.Concurrent.silent_saved_step
