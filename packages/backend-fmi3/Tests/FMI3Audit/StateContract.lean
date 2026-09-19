import RumocaFMI3.StateContract
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.StateContract.

#audit axioms Rumoca.FMI3.StateCalls.Events.get_behaviors
#audit axioms Rumoca.FMI3.StateCalls.Events.set_behaviors
#audit axioms Rumoca.FMI3.StateCalls.failure_execution_correct
#audit axioms Rumoca.FMI3.StateCalls.silent_execution_correct
#audit axioms Rumoca.FMI3.StateCalls.quiet_execution_correct
#audit axioms Rumoca.FMI3.StateCalls.failure_message_collected
#audit axioms Rumoca.FMI3.StateCalls.prepared_correct
#audit axioms Rumoca.FMI3.StateCalls.rendered_contract
#audit axioms Rumoca.FMI3.StateCalls.QuietExecutionContract.get_refines
#audit axioms Rumoca.FMI3.StateCalls.QuietExecutionContract.set_refines
