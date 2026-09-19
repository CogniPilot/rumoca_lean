import TensorCChecks.Entry
import ProofAudit.Audit

-- Axiom audit for the roots defined in TensorCChecks.Entry.

#audit axioms Rumoca.CTensor.ProgramFixture.Entry.reads_input
#audit axioms Rumoca.CTensor.ProgramFixture.Entry.reads_state
#audit axioms Rumoca.CTensor.ProgramFixture.Entry.writable
#audit axioms Rumoca.CTensor.ProgramFixture.Entry.arguments_valid
#audit axioms Rumoca.CTensor.ProgramFixture.Entry.named_bound
#audit axioms Rumoca.CTensor.ProgramFixture.Entry.layout_bound
#audit axioms Rumoca.CTensor.ProgramFixture.Entry.represented
#audit axioms Rumoca.CTensor.ProgramFixture.Entry.ready
#audit axioms Rumoca.CTensor.ProgramFixture.Entry.call_correct
#audit axioms Rumoca.CTensor.ProgramFixture.Entry.artifact_correct
