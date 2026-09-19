import RumocaC.CallSites
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.CallSites.

#audit axioms Rumoca.CCallSites.checkFunction_correct
#audit axioms Rumoca.CCallSites.checkStatement_correct
#audit axioms Rumoca.CCallSites.concurrent_reaches
#audit axioms Rumoca.CCallSites.concurrent_ready
#audit axioms Rumoca.CCallSites.enter_ready
#audit axioms Rumoca.CCallSites.event_ready
#audit axioms Rumoca.CCallSites.internal_ready
#audit axioms Rumoca.CCallSites.loop_ready_next
#audit axioms Rumoca.CCallSites.named_resolution
#audit axioms Rumoca.CCallSites.operand_permitted
#audit axioms Rumoca.CCallSites.reaches_ready
#audit axioms Rumoca.CCallSites.ready_withHeap
#audit axioms Rumoca.CCallSites.resume_ready
