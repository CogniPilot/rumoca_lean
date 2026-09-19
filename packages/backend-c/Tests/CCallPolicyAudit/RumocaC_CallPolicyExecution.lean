import RumocaC.CallPolicyExecution
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.CallPolicyExecution.

#audit axioms Rumoca.CCallPolicy.entered_internal_edge
#audit axioms Rumoca.CCallPolicy.internal_resolution
#audit axioms Rumoca.CCallPolicy.scheduled_internal_decreases
#audit axioms Rumoca.CCallPolicy.scheduled_internal_edge
