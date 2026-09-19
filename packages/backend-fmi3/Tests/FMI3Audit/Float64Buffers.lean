import RumocaFMI3.Float64Buffers
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.Float64Buffers.

#audit axioms Rumoca.FMI3.Float64Buffers.Stored.preserved
#audit axioms Rumoca.FMI3.Float64Buffers.different_blocks
#audit axioms Rumoca.FMI3.Float64Buffers.reference_converts
#audit axioms Rumoca.FMI3.Float64Buffers.references_run
#audit axioms Rumoca.FMI3.Float64Buffers.references_read
#audit axioms Rumoca.FMI3.Float64Buffers.references_frame
#audit axioms Rumoca.FMI3.Float64Buffers.references_preserve
#audit axioms Rumoca.FMI3.Float64Buffers.finite_written
#audit axioms Rumoca.FMI3.Float64Buffers.values_run
#audit axioms Rumoca.FMI3.Float64Buffers.values_preserve
