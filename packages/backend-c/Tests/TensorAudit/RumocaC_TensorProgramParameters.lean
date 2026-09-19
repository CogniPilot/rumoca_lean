import RumocaC.TensorProgramParameters
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.TensorProgramParameters.

#audit axioms Rumoca.CTensor.Lowering.Arguments.locals_absent
#audit axioms Rumoca.CTensor.Lowering.Arguments.locals_present
#audit axioms Rumoca.CTensor.Lowering.Arguments.types_absent
#audit axioms Rumoca.CTensor.Lowering.Arguments.header_type
#audit axioms Rumoca.CTensor.Lowering.Arguments.cast_admissible
#audit axioms Rumoca.CTensor.Lowering.Arguments.bind_parameters
#audit axioms Rumoca.CTensor.Lowering.Arguments.bind_types
