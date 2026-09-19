import TensorCChecks.IVPEntry
import ProofAudit.Audit

-- Axiom audit for the roots defined in TensorCChecks.IVPEntry.

#audit axioms Rumoca.CTensor.ProgramFixture.IVPEntry.plan_valid
#audit axioms Rumoca.CTensor.ProgramFixture.IVPEntry.initial_result
#audit axioms Rumoca.CTensor.ProgramFixture.IVPEntry.derivative_result
#audit axioms Rumoca.CTensor.ProgramFixture.IVPEntry.jacobian_function
#audit axioms Rumoca.CTensor.ProgramFixture.IVPEntry.sources_shape
#audit axioms Rumoca.CTensor.ProgramFixture.IVPEntry.program_correct
#audit axioms Rumoca.CTensor.ProgramFixture.IVPEntry.initial_arguments
#audit axioms Rumoca.CTensor.ProgramFixture.IVPEntry.derivative_arguments
#audit axioms Rumoca.CTensor.ProgramFixture.IVPEntry.parameter_bound
#audit axioms Rumoca.CTensor.ProgramFixture.IVPEntry.initial_call_correct
#audit axioms Rumoca.CTensor.ProgramFixture.IVPEntry.derivative_call_correct
#audit axioms Rumoca.CTensor.ProgramFixture.IVPEntry.artifact_correct
#audit axioms Rumoca.CTensor.ProgramFixture.IVPEntry.jacobianDiag_correct
