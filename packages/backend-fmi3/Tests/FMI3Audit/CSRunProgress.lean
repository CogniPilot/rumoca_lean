import RumocaFMI3.CSRunProgress
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.CSRunProgress.

#audit axioms Rumoca.FMI3.CSRun.ActionContract.realizes
#audit axioms Rumoca.FMI3.CSRun.ActionContract.performed_iff
#audit axioms Rumoca.FMI3.CSRun.ActionContract.faulted_iff
#audit axioms Rumoca.FMI3.CSRun.ActionContract.progress
#audit axioms Rumoca.FMI3.CSRun.ActionContract.faulted_step
#audit axioms Rumoca.FMI3.CSRun.LoggedTrace.progress
