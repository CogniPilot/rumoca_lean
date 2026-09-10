import ProofAudit.Audit
import RumocaC.TensorCallContract
import RumocaC.TensorFillContract

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
#audit axioms Rumoca.CLoops.Calls.body_reaches
#audit axioms Rumoca.CLoops.Calls.call_reaches
#audit axioms Rumoca.CLoops.Calls.call_behaviors
#audit axioms Rumoca.CLoops.Calls.resume_caller
#audit axioms Rumoca.CTensor.bind_parameters
#audit axioms Rumoca.CTensor.bind_types
#audit axioms Rumoca.CTensor.helper_call_reaches
#audit axioms Rumoca.CTensor.helper_call_correct
#audit axioms Rumoca.CTensor.invoke_reaches
#audit axioms Rumoca.CTensor.call_artifact_correct
#audit axioms Rumoca.CTensor.writer_reaches
#audit axioms Rumoca.CTensor.function_reaches
#audit axioms Rumoca.CTensor.Fill.function_reaches
#audit axioms Rumoca.CTensor.Fill.bind_parameters
#audit axioms Rumoca.CTensor.Fill.bind_types
#audit axioms Rumoca.CTensor.Fill.helper_call_correct
#audit axioms Rumoca.CTensor.Fill.invoke_reaches
#audit axioms Rumoca.CTensor.Fill.literal_eval
#audit axioms Rumoca.CTensor.Fill.solve_fill_correct
#audit axioms Rumoca.CTensor.Fill.Syntax.render_denotes
#audit axioms Rumoca.CTensor.Fill.artifact_correct
