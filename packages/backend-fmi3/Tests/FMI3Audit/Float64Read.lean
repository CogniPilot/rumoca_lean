import RumocaFMI3.Float64Read
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.Float64Read.

#audit axioms Rumoca.FMI3.Float64Calls.variable_code_unique
#audit axioms Rumoca.FMI3.Float64Calls.variable_of_valid
#audit axioms Rumoca.FMI3.Float64Calls.read_dispatch
#audit axioms Rumoca.FMI3.Float64Calls.output_address
#audit axioms Rumoca.FMI3.Float64Calls.derivative_call
#audit axioms Rumoca.FMI3.Float64Calls.output_return
#audit axioms Rumoca.FMI3.Float64Calls.read_iteration
#audit axioms Rumoca.FMI3.Float64Calls.outputValues_at
#audit axioms Rumoca.FMI3.Float64Calls.pending_output
#audit axioms Rumoca.FMI3.Float64Calls.write_next_output
#audit axioms Rumoca.FMI3.Float64Calls.references_written
#audit axioms Rumoca.FMI3.Float64Calls.state_written
#audit axioms Rumoca.FMI3.Float64Calls.time_written
#audit axioms Rumoca.FMI3.Float64Calls.selectReference_correct
#audit axioms Rumoca.FMI3.Float64Calls.read_reaches
