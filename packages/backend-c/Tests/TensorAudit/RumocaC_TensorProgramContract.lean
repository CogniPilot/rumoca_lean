import RumocaC.TensorProgramContract
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.TensorProgramContract.

#audit axioms Rumoca.CTensor.Lowering.body_correct
#audit axioms Rumoca.CTensor.Lowering.artifact_correct

#audit axioms Rumoca.CTensor.Lowering.body_correct_for
#audit axioms Rumoca.CTensor.Lowering.artifact_correct_for
#audit axioms Rumoca.CTensor.Lowering.BodyCorrectFor.to_full
#audit axioms Rumoca.CTensor.Lowering.ArtifactContractFor.to_full
