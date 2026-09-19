import RumocaFMI3.MECountExecution
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.MECountExecution.

#audit axioms Rumoca.FMI3.MECountCalls.configuration_frame
#audit axioms Rumoca.FMI3.MECountCalls.Memory.success
#audit axioms Rumoca.FMI3.MECountCalls.Memory.failure
#audit axioms Rumoca.FMI3.MECountCalls.Contract.quiet
#audit axioms Rumoca.FMI3.MECountCalls.execution
