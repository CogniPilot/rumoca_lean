import RumocaFMI3.MEMixedInterrupted
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.MEMixedInterrupted.

#audit axioms Rumoca.FMI3.MEMixedRun.Completed.stopped
#audit axioms Rumoca.FMI3.MEMixedRun.Interrupted.stopped
#audit axioms Rumoca.FMI3.MEMixedRun.Stopped.interrupted
#audit axioms Rumoca.FMI3.MEMixedRun.interrupted_iff
#audit axioms Rumoca.FMI3.MEMixedRun.ReferenceTrace.split
#audit axioms Rumoca.FMI3.MEMixedRun.Trace.take
#audit axioms Rumoca.FMI3.MEMixedRun.Trace.after_prefix
