import RumocaC.TensorSquareDiagonal
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.TensorSquareDiagonal.

#audit axioms Rumoca.CTensor.SquareDiagonal.copy_step
#audit axioms Rumoca.CTensor.SquareDiagonal.coeff_reads
#audit axioms Rumoca.CTensor.SquareDiagonal.loop_reaches
#audit axioms Rumoca.CTensor.SquareDiagonal.function_reaches
#audit axioms Rumoca.CTensor.SquareDiagonal.helper_call_reaches
#audit axioms Rumoca.CTensor.SquareDiagonal.helper_call_correct
#audit axioms Rumoca.CTensor.SquareDiagonal.invoke_reaches
#audit axioms Rumoca.CTensor.SquareDiagonal.output_reads
#audit axioms Rumoca.CTensor.SquareDiagonal.output_frame
#audit axioms Rumoca.CTensor.SquareDiagonal.diagonal_nearest
#audit axioms Rumoca.CTensor.SquareDiagonal.matrix_diagonal_nearest
