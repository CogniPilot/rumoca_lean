import RumocaFMI3.MEMixedExecution
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.MEMixedExecution.

#audit axioms Rumoca.FMI3.MEMixedRun.run_correct
#audit axioms Rumoca.FMI3.MEMixedRun.action_correct
#audit axioms Rumoca.FMI3.MEMixedRun.trace_correct
#audit axioms Rumoca.FMI3.MEMixedRun.retained_field_outside
#audit axioms Rumoca.FMI3.MEMixedRun.Returned.of_frame
