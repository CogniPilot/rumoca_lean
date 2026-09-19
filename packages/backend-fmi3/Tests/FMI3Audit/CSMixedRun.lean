import RumocaFMI3.CSMixedRun
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.CSMixedRun.

#audit axioms Rumoca.FMI3.CSMixedRun.Action.Prepared.framed
#audit axioms Rumoca.FMI3.CSMixedRun.ActionContract.faulted_iff
#audit axioms Rumoca.FMI3.CSMixedRun.ActionContract.performed_iff
#audit axioms Rumoca.FMI3.CSMixedRun.ActionContract.progress
#audit axioms Rumoca.FMI3.CSMixedRun.ActionContract.realizes
#audit axioms Rumoca.FMI3.CSMixedRun.ActionContract.returned
#audit axioms Rumoca.FMI3.CSMixedRun.Trace.callerFrame
#audit axioms Rumoca.FMI3.CSMixedRun.Trace.completed
#audit axioms Rumoca.FMI3.CSMixedRun.Trace.progress
#audit axioms Rumoca.FMI3.CSMixedRun.Trace.storage
#audit axioms Rumoca.FMI3.CSMixedRun.loggingUpdate_cons_getD
