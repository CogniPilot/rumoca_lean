import RumocaC.TensorIVPContract
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.TensorIVPContract.

#audit axioms Rumoca.CTensor.Lowering.ProgramEntry.correct
#audit axioms Rumoca.CTensor.Lowering.DiagonalEntry.correct
#audit axioms Rumoca.CTensor.Lowering.OptionalDiagonalEntry.correct
#audit axioms Rumoca.CTensor.Lowering.PointwisePlan.correct
