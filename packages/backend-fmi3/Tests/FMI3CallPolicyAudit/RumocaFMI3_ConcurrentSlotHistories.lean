import RumocaFMI3.ConcurrentSlotHistories
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.ConcurrentSlotHistories.

#audit axioms Rumoca.FMI3.ConcurrentSlots.Claim.target
#audit axioms Rumoca.FMI3.ConcurrentSlots.ScheduledStep.erases
#audit axioms Rumoca.FMI3.ConcurrentSlots.ScheduledStep.refines
#audit axioms Rumoca.FMI3.ConcurrentSlots.history_refines
#audit axioms Rumoca.FMI3.ConcurrentSlots.owner_history_keeps
#audit axioms Rumoca.FMI3.ConcurrentSlots.owner_step_keeps
#audit axioms Rumoca.FMI3.ConcurrentSlots.reclaim_requires_release
#audit axioms Rumoca.FMI3.ConcurrentSlots.scheduled_reclaim_requires_release
