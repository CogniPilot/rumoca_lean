import RumocaC.TensorTypedContract
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.TensorTypedContract.

#audit axioms Rumoca.CTensor.Lowering.typed_call_correct
#audit axioms Rumoca.CTensor.Lowering.typed_diagonal_call_correct

#audit axioms Rumoca.CTensor.Lowering.TypedBridge.typed_call_correct_with
#audit axioms Rumoca.CTensor.Lowering.TypedBridge.typed_diagonal_call_correct_with
#audit axioms Rumoca.CTensor.Lowering.typed_call_correct_for
#audit axioms Rumoca.CTensor.Lowering.typed_diagonal_call_correct_for
#audit axioms Rumoca.CTensor.Lowering.TypedCallCorrectFor.to_full
#audit axioms Rumoca.CTensor.Lowering.TypedDiagonalCallCorrectFor.to_full
