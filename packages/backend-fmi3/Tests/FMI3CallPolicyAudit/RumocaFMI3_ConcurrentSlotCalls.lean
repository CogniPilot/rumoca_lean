import RumocaFMI3.ConcurrentSlotCalls
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.ConcurrentSlotCalls.

#audit axioms Rumoca.FMI3.ConcurrentSlots.claim_busy
#audit axioms Rumoca.FMI3.ConcurrentSlots.claim_success
#audit axioms Rumoca.FMI3.ConcurrentSlots.release_scheduled
#audit axioms Rumoca.FMI3.ConcurrentSlots.reserve_operation
#audit axioms Rumoca.FMI3.ConcurrentSlots.reserve_scheduled
