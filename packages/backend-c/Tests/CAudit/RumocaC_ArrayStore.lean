import RumocaC.ArrayStore
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.ArrayStore.

#audit axioms Rumoca.CMemory.ArrayStore.written_at
#audit axioms Rumoca.CMemory.ArrayStore.frame
#audit axioms Rumoca.CMemory.ArrayStore.run_written
#audit axioms Rumoca.CMemory.ArrayStore.run_preserves
#audit axioms Rumoca.CMemory.ArrayStore.written_reads
