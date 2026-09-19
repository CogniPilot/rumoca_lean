import RumocaC.CallContext
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.CallContext.

#audit axioms Rumoca.CCalls.Context.active_of_suspended
#audit axioms Rumoca.CCalls.Context.append_eq_outer
#audit axioms Rumoca.CCalls.Context.appended_heap
#audit axioms Rumoca.CCalls.Context.depth_append
#audit axioms Rumoca.CCalls.Context.enter_append
#audit axioms Rumoca.CCalls.Context.heap_append
#audit axioms Rumoca.CCalls.Context.internal_append
#audit axioms Rumoca.CCalls.Context.returned_local
#audit axioms Rumoca.CCalls.Context.step_append
#audit axioms Rumoca.CCalls.Context.step_unappend
