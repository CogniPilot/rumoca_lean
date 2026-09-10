import ProofAudit.Audit
import RumocaC.TensorContract

#audit axioms Rumoca.CArithmetic.floatMul_finite
#audit axioms Rumoca.CLoops.increment_exact
#audit axioms Rumoca.CLoops.loop_reaches
#audit axioms Rumoca.CMemory.TensorView.store_next
#audit axioms Rumoca.CMemory.TensorView.written_reads
#audit axioms Rumoca.CMemory.TensorView.written_frame
#audit axioms Rumoca.CTensor.function_correct
#audit axioms Rumoca.CTensor.Syntax.render_denotes
#audit axioms Rumoca.CTensor.Syntax.denotes_unique
#audit axioms Rumoca.CTensor.body_correct
#audit axioms Rumoca.CTensor.artifact_correct
