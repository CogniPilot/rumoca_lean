import RumocaFMI3.SlotOwners
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.SlotOwners.

#audit axioms Rumoca.FMI3.SlotOwners.reserve_refines
#audit axioms Rumoca.FMI3.SlotOwners.release_refines
#audit axioms Rumoca.FMI3.SlotOwners.only_owner_releases
#audit axioms Rumoca.FMI3.SlotOwners.reserved_excludes
#audit axioms Rumoca.FMI3.SlotOwners.initialized
#audit axioms Rumoca.FMI3.SlotOwners.exchange_reserves
#audit axioms Rumoca.FMI3.SlotOwners.exchange_busy
#audit axioms Rumoca.FMI3.SlotOwners.write_releases
#audit axioms Rumoca.FMI3.SlotOwners.internal_preserves
