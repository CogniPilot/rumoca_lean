import RumocaC.TensorEncodedDiagonal
import ProofAudit.Audit

#audit axioms Rumoca.CTensor.EncodedDiagonal.matrix_get
#audit axioms Rumoca.CTensor.EncodedDiagonal.scatter_at
#audit axioms Rumoca.CTensor.EncodedDiagonal.scatter_frame
#audit axioms Rumoca.CTensor.EncodedDiagonal.scatter_store_next
#audit axioms Rumoca.CTensor.EncodedDiagonal.result_reads
#audit axioms Rumoca.CTensor.EncodedDiagonal.result_frame
#audit axioms Rumoca.CTensor.EncodedDiagonal.coeff_reads
#audit axioms Rumoca.CTensor.EncodedDiagonal.finiteBits_get
#audit axioms Rumoca.CTensor.EncodedDiagonal.scatter_finite
#audit axioms Rumoca.CTensor.EncodedDiagonal.resultHeap_finite
