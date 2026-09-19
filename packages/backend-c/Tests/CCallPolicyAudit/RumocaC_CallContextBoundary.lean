import RumocaC.CallContextBoundary
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.CallContextBoundary.

#audit axioms Rumoca.CCalls.Context.live_heap
#audit axioms Rumoca.CCalls.Context.step_live
#audit axioms Rumoca.CCalls.Context.suspended_call
#audit axioms Rumoca.CCalls.Context.suspended_heap
#audit axioms Rumoca.CCalls.Context.suspended_step
