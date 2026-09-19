import RumocaFMI3.CSRunLogging
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.CSRunLogging.

#audit axioms Rumoca.FMI3.CSRun.Retains.logger
#audit axioms Rumoca.FMI3.CSRun.ProtectedFrame.run
#audit axioms Rumoca.FMI3.CSRun.ProtectedFrame.retains
#audit axioms Rumoca.FMI3.CSRun.ProtectedFrame.owners
#audit axioms Rumoca.FMI3.CSRun.ActionContract.step_behaviors
#audit axioms Rumoca.FMI3.CSRun.ActionContract.returned
#audit axioms Rumoca.FMI3.CSRun.ActionContract.restart_returned
#audit axioms Rumoca.FMI3.CSRun.LoggedTrace.completed
#audit axioms Rumoca.FMI3.CSRun.LoggedTrace.storage
#audit axioms Rumoca.FMI3.CSRun.Logger.FramePolicy.storage
#audit axioms Rumoca.FMI3.CSRun.LoggedTrace.frame
