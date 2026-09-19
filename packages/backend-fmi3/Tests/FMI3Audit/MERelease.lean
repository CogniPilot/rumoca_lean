import RumocaFMI3.MERelease
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.MERelease.

#audit axioms Rumoca.FMI3.MEHistory.Action.next_live
#audit axioms Rumoca.FMI3.MEHistory.ReferenceTrace.live
#audit axioms Rumoca.FMI3.MEHistory.ReferenceState.Live.terminate
#audit axioms Rumoca.FMI3.MEHistory.slot_outside
#audit axioms Rumoca.FMI3.MEHistory.release_correct
