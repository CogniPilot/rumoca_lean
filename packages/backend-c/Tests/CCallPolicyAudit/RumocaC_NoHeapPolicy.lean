import RumocaC.NoHeapPolicy
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.NoHeapPolicy.

#audit axioms Rumoca.CCallPolicy.checkFunction_mono
#audit axioms Rumoca.CCallPolicy.noHeap_callee_named
#audit axioms Rumoca.CCallPolicy.noHeap_body_ready
#audit axioms Rumoca.CCallPolicy.noHeap_no_alloc_call
#audit axioms Rumoca.CCallPolicy.noHeap_execution_no_alloc
#audit axioms Rumoca.CCallPolicy.definedEdge_decreases
#audit axioms Rumoca.CCallPolicy.acyclic_of_ranked
