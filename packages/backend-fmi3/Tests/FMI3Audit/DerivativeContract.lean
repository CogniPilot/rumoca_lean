import RumocaFMI3.DerivativeContract
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.DerivativeContract.

#audit axioms Rumoca.FMI3.DerivativeCalls.failure_execution_correct
#audit axioms Rumoca.FMI3.DerivativeCalls.silent_execution_correct
#audit axioms Rumoca.FMI3.DerivativeCalls.quiet_execution_correct
#audit axioms Rumoca.FMI3.DerivativeCalls.failure_message_collected
#audit axioms Rumoca.FMI3.DerivativeCalls.prepared_correct
#audit axioms Rumoca.FMI3.DerivativeCalls.rendered_contract
#audit axioms Rumoca.FMI3.DerivativeCalls.QuietExecutionContract.get_refines
