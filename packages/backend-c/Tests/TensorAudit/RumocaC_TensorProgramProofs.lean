import RumocaC.TensorProgramProofs
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.TensorProgramProofs.

#audit axioms Rumoca.CTensor.Lowering.emit_correct
#audit axioms Rumoca.CTensor.Lowering.emit_refines

#audit axioms Rumoca.CTensor.Lowering.Setup.restrict
#audit axioms Rumoca.CTensor.Lowering.SetupFor.weaken
#audit axioms Rumoca.CTensor.Lowering.emit_correct_for
#audit axioms Rumoca.CTensor.Lowering.emit_refines_for
