import RumocaC.Memory
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.Memory.

#audit axioms Rumoca.CMemory.Value.isFinite_finite
#audit axioms Rumoca.CMemory.store_float64
#audit axioms Rumoca.CMemory.store_frame
#audit axioms Rumoca.CMemory.store_other_block
#audit axioms Rumoca.CMemory.store_unallocated
#audit axioms Rumoca.CMemory.store_readonly
#audit axioms Rumoca.CMemory.Address.member_inj
