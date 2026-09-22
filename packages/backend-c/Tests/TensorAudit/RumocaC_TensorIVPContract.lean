import RumocaC.TensorIVPContract
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.TensorIVPContract.

#audit axioms Rumoca.CTensor.Lowering.ProgramEntry.correct
#audit axioms Rumoca.CTensor.Lowering.DiagonalEntry.correct
#audit axioms Rumoca.CTensor.Lowering.OptionalDiagonalEntry.correct
#audit axioms Rumoca.CTensor.Lowering.PointwisePlan.correct

#audit axioms Rumoca.CTensor.Lowering.ProgramEntry.correct_for
#audit axioms Rumoca.CTensor.Lowering.DiagonalEntry.correct_for
#audit axioms Rumoca.CTensor.Lowering.OptionalDiagonalEntry.correct_for
#audit axioms Rumoca.CTensor.Lowering.PointwisePlan.correct_for
#audit axioms Rumoca.CTensor.Lowering.ProgramEntry.ContractFor.to_full
#audit axioms Rumoca.CTensor.Lowering.DiagonalEntry.ContractFor.to_full
#audit axioms Rumoca.CTensor.Lowering.OptionalDiagonalEntry.ContractFor.to_full
#audit axioms Rumoca.CTensor.Lowering.PointwisePlan.ContractFor.to_full
