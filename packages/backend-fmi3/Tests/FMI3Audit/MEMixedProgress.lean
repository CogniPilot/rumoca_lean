import RumocaFMI3.MEMixedProgress
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.MEMixedProgress.

#audit axioms Rumoca.FMI3.MENumericalRun.Calls.not_faulted
#audit axioms Rumoca.FMI3.MEMixedRun.ActionContract.performed_iff
#audit axioms Rumoca.FMI3.MEMixedRun.ActionContract.faulted_iff
#audit axioms Rumoca.FMI3.MEMixedRun.ActionContract.faulted_rejection
#audit axioms Rumoca.FMI3.MEMixedRun.ActionContract.progress
#audit axioms Rumoca.FMI3.MEMixedRun.Trace.progress
