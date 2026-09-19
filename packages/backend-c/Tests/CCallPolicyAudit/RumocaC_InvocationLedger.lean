import RumocaC.InvocationLedger
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.InvocationLedger.

#audit axioms Rumoca.CCalls.Host.Recording.advance_fresh
#audit axioms Rumoca.CCalls.Host.Recording.aligned_active
#audit axioms Rumoca.CCalls.Host.Recording.history_erases
#audit axioms Rumoca.CCalls.Host.Recording.history_invariants
#audit axioms Rumoca.CCalls.Host.Recording.history_issued
#audit axioms Rumoca.CCalls.Host.Recording.history_lift
#audit axioms Rumoca.CCalls.Host.Recording.initial_aligned
#audit axioms Rumoca.CCalls.Host.Recording.initial_fresh
#audit axioms Rumoca.CCalls.Host.Recording.step_aligned
