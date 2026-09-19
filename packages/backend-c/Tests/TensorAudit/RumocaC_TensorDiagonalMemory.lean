import RumocaC.TensorDiagonalMemory
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.TensorDiagonalMemory.

#audit axioms Rumoca.CTensor.Diagonal.matrix_get
#audit axioms Rumoca.CTensor.Diagonal.matrix_index
#audit axioms Rumoca.CTensor.Diagonal.position_index
#audit axioms Rumoca.CTensor.Diagonal.position_bound
#audit axioms Rumoca.CTensor.Diagonal.position_injective
#audit axioms Rumoca.CTensor.Diagonal.counter_bounds
#audit axioms Rumoca.CTensor.Diagonal.position_bounded
#audit axioms Rumoca.CTensor.Diagonal.scatter_at
#audit axioms Rumoca.CTensor.Diagonal.scatter_frame
#audit axioms Rumoca.CTensor.Diagonal.scatter_store_next
#audit axioms Rumoca.CTensor.Diagonal.zero_writable
#audit axioms Rumoca.CTensor.Diagonal.result_reads
#audit axioms Rumoca.CTensor.Diagonal.result_frame
#audit axioms Rumoca.CTensor.Diagonal.input_reads
#audit axioms Rumoca.CTensor.Diagonal.solve_matrix
