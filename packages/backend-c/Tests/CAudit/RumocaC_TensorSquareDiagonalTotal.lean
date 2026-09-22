import RumocaC.TensorSquareDiagonalTotal
import ProofAudit.Audit

#audit axioms Rumoca.CTensor.SquareDiagonal.Total.result_get
#audit axioms Rumoca.CTensor.SquareDiagonal.Total.result_spec
#audit axioms Rumoca.CTensor.SquareDiagonal.Total.result_no_nan
#audit axioms Rumoca.CTensor.SquareDiagonal.Total.result_finite
#audit axioms Rumoca.CTensor.SquareDiagonal.Total.copy_step
#audit axioms Rumoca.CTensor.SquareDiagonal.Total.loop_reaches
#audit axioms Rumoca.CTensor.SquareDiagonal.Total.tail_reaches
#audit axioms Rumoca.CTensor.SquareDiagonal.Total.function_reaches
#audit axioms Rumoca.CTensor.SquareDiagonal.Total.helper_call_reaches
#audit axioms Rumoca.CTensor.SquareDiagonal.Total.helper_call_correct
