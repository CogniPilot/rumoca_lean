import RumocaFMI3.Float64Contract
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.Float64Contract.

#audit axioms Rumoca.FMI3.Float64Calls.failure_execution_correct
#audit axioms Rumoca.FMI3.Float64Calls.silent_execution_correct
#audit axioms Rumoca.FMI3.Float64Calls.quiet_execution_correct
#audit axioms Rumoca.FMI3.Float64Calls.failure_message_collected
#audit axioms Rumoca.FMI3.Float64Calls.prepared_correct
#audit axioms Rumoca.FMI3.Float64Calls.rendered_contract
#audit axioms Rumoca.FMI3.Float64Calls.QuietExecutionContract.get_refines
#audit axioms Rumoca.FMI3.Float64Calls.metadata_selection
