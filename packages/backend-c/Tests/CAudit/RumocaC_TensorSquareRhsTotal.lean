import RumocaC.TensorSquareRhsTotalContract
import ProofAudit.Audit

#audit axioms Rumoca.CTensor.MultiplicationTotal.invoke_reaches
#audit axioms Rumoca.CTensor.MultiplicationTotal.entry_reaches
#audit axioms Rumoca.CTensor.MultiplicationTotal.entry_correct
#audit axioms Rumoca.CTensor.MultiplicationTotal.entry_context
#audit axioms Rumoca.CTensor.SquareRhsTotal.reads
#audit axioms Rumoca.CTensor.SquareRhsTotal.frame
#audit axioms Rumoca.CTensor.SquareRhsTotal.writable
#audit axioms Rumoca.CTensor.SquareRhsTotal.finite_heap
#audit axioms Rumoca.CTensor.SquareRhsTotal.finite_execution
#audit axioms Rumoca.CTensor.SquareRhsTotal.detects_overflow
#audit axioms Rumoca.CTensor.SquareRhsTotal.call_reaches
#audit axioms Rumoca.CTensor.SquareRhsTotal.call_correct
#audit axioms Rumoca.CTensor.SquareRhsTotal.call_context
#audit axioms Rumoca.CTensor.SquareRhsTotal.storage_correct
#audit axioms Rumoca.CTensor.SquareRhsTotal.closed_free
#audit axioms Rumoca.CTensor.SquareRhsTotal.closed_storage
#audit axioms Rumoca.CTensor.SquareRhsTotal.artifact_correct
#audit axioms Rumoca.CTensor.SquareRhsTotal.linked_artifact_correct
