import RumocaFMI3.Float64SetContract
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.Float64SetContract.

#audit axioms Rumoca.FMI3.Float64Set.failure_execution_correct
#audit axioms Rumoca.FMI3.Float64Set.silent_execution_correct
#audit axioms Rumoca.FMI3.Float64Set.quiet_execution_correct
#audit axioms Rumoca.FMI3.Float64Set.QuietExecutionContract.set_refines
#audit axioms Rumoca.FMI3.Float64Set.failure_message_collected
#audit axioms Rumoca.FMI3.Float64Set.prepared_correct
#audit axioms Rumoca.FMI3.Float64Set.rendered_contract
#audit axioms Rumoca.FMI3.Float64Set.metadata_selection
