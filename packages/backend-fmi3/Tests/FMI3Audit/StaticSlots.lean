import RumocaFMI3.StaticSlots
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.StaticSlots.

#audit axioms Rumoca.FMI3.StaticSlots.reserve_iff
#audit axioms Rumoca.FMI3.StaticSlots.reserve_busy
#audit axioms Rumoca.FMI3.StaticSlots.reserve_frame
#audit axioms Rumoca.FMI3.StaticSlots.cannot_reserve_twice
#audit axioms Rumoca.FMI3.StaticSlots.consecutive_distinct
#audit axioms Rumoca.FMI3.StaticSlots.full_iff
#audit axioms Rumoca.FMI3.StaticSlots.release_iff
#audit axioms Rumoca.FMI3.StaticSlots.release_vacant
#audit axioms Rumoca.FMI3.StaticSlots.release_frame
#audit axioms Rumoca.FMI3.StaticSlots.release_after_reserve
#audit axioms Rumoca.FMI3.StaticSlots.reusable
#audit axioms Rumoca.FMI3.StaticSlots.update_commutes
#audit axioms Rumoca.FMI3.StaticSlots.findFree_sound
#audit axioms Rumoca.FMI3.StaticSlots.findFree_none_iff
#audit axioms Rumoca.FMI3.StaticSlots.findFree_exhausted
#audit axioms Rumoca.FMI3.StaticSlots.findFree_reserves
