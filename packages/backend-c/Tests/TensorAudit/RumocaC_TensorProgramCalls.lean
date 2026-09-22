import RumocaC.TensorProgramCalls
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.TensorProgramCalls.

#audit axioms Rumoca.CTensor.Lowering.valid_nodup
#audit axioms Rumoca.CTensor.Lowering.helper_absent
#audit axioms Rumoca.CTensor.Lowering.Library.setup
#audit axioms Rumoca.CTensor.Lowering.program_call_reaches
#audit axioms Rumoca.CTensor.Lowering.program_call_refines

#audit axioms Rumoca.CTensor.Lowering.Library.restrict
#audit axioms Rumoca.CTensor.Lowering.LibraryFor.weaken
#audit axioms Rumoca.CTensor.Lowering.LibraryFor.setup
#audit axioms Rumoca.CTensor.Lowering.program_call_reaches_for
#audit axioms Rumoca.CTensor.Lowering.program_call_refines_for
