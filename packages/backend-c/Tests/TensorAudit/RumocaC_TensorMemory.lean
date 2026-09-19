import RumocaC.TensorMemory
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.TensorMemory.

#audit axioms Rumoca.CMemory.TensorView.store_next
#audit axioms Rumoca.CMemory.TensorView.written_reads
#audit axioms Rumoca.CMemory.TensorView.written_frame
#audit axioms Rumoca.CMemory.TensorView.written_writable
#audit axioms Rumoca.CMemory.TensorView.written_preserves_writable
