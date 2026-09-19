import RumocaC.TensorFillProofs
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.TensorFillProofs.

#audit axioms Rumoca.CTensor.Fill.function_reaches
#audit axioms Rumoca.CTensor.Fill.bind_parameters
#audit axioms Rumoca.CTensor.Fill.bind_types
#audit axioms Rumoca.CTensor.Fill.helper_call_correct
#audit axioms Rumoca.CTensor.Fill.invoke_reaches
#audit axioms Rumoca.CTensor.Fill.literal_eval
#audit axioms Rumoca.CTensor.Fill.solve_fill_correct
