import RumocaFMI3.CSMixedLifecycle
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.CSMixedLifecycle.

#audit axioms Rumoca.FMI3.CSMixedRun.Change.can_finish
#audit axioms Rumoca.FMI3.CSMixedRun.Change.rehandle
#audit axioms Rumoca.FMI3.CSMixedRun.ReferenceTrace.can_finish
#audit axioms Rumoca.FMI3.CSMixedRun.ReferenceTrace.rehandle
#audit axioms Rumoca.FMI3.CSMixedRun.Trace.released
#audit axioms Rumoca.FMI3.CSMixedRun.Trace.released_frame
