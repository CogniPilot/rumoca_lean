import RumocaFMI3.CSRunInterrupted
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.CSRunInterrupted.

#audit axioms Rumoca.FMI3.CSRun.Recorded.stopped
#audit axioms Rumoca.FMI3.CSRun.Interrupted.stopped
#audit axioms Rumoca.FMI3.CSRun.Stopped.interrupted
#audit axioms Rumoca.FMI3.CSRun.interrupted_iff
#audit axioms Rumoca.FMI3.CSRun.ReferenceTrace.split
