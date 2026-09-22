import RumocaC.LoopCallSites
import ProofAudit.Audit

#audit axioms Rumoca.CCallSites.LoopCalls.enter_ready
#audit axioms Rumoca.CCallSites.LoopCalls.ready_next
#audit axioms Rumoca.CCallSites.LoopCalls.ready_reaches
#audit axioms Rumoca.CCallSites.LoopCalls.ready_resolves
#audit axioms Rumoca.CCallSites.LoopCalls.reachable_resolves
#audit axioms Rumoca.CCallSites.LoopCalls.call_resolves
#audit axioms Rumoca.CCallSites.LoopCalls.call_terminates_events
