import RumocaC.MemoryFootprint
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.MemoryFootprint.

#audit axioms Rumoca.CMemory.Footprint.load_eq
#audit axioms Rumoca.CMemory.Footprint.replace_eq
#audit axioms Rumoca.CMemory.Footprint.store_outside
#audit axioms Rumoca.CMemory.Footprint.store_region
#audit axioms Rumoca.CMemory.Footprint.store_transport
