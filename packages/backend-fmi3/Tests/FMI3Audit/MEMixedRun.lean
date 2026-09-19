import RumocaFMI3.MEMixedRun
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.MEMixedRun.

#audit axioms Rumoca.FMI3.MEMixedRun.ActionContract.realizes
#audit axioms Rumoca.FMI3.MEMixedRun.ActionContract.returned
#audit axioms Rumoca.FMI3.MEMixedRun.Trace.completed
#audit axioms Rumoca.FMI3.MEMixedRun.Trace.storage
#audit axioms Rumoca.FMI3.MEMixedRun.Action.Prepared.preserved
#audit axioms Rumoca.FMI3.MEMixedRun.Trace.callerFrame
#audit axioms Rumoca.FMI3.MEMixedRun.loggingUpdate_cons_getD
