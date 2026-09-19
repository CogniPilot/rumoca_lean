import RumocaFMI3.AtomicSlots
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.AtomicSlots.

#audit axioms Rumoca.FMI3.AtomicSlots.initialized
#audit axioms Rumoca.FMI3.AtomicSlots.exchange_exists
#audit axioms Rumoca.FMI3.AtomicSlots.reserve_corresponds
#audit axioms Rumoca.FMI3.AtomicSlots.release_exists
#audit axioms Rumoca.FMI3.AtomicSlots.scan_ready
#audit axioms Rumoca.FMI3.AtomicSlots.scan_reserves
#audit axioms Rumoca.FMI3.AtomicSlots.scan_exhausted
