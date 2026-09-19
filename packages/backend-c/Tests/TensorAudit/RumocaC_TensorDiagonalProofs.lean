import RumocaC.TensorDiagonalProofs
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.TensorDiagonalProofs.

#audit axioms Rumoca.CTensor.Diagonal.bind_valid
#audit axioms Rumoca.CTensor.Diagonal.copy_step
#audit axioms Rumoca.CTensor.Diagonal.offset_eval
#audit axioms Rumoca.CTensor.Diagonal.offset_step
#audit axioms Rumoca.CTensor.Diagonal.loop_reaches
#audit axioms Rumoca.CTensor.Diagonal.initialize_reaches
#audit axioms Rumoca.CTensor.Diagonal.tail_reaches
