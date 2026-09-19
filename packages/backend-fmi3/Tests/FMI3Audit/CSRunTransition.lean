import RumocaFMI3.CSRunTransition
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.CSRunTransition.

#audit axioms Rumoca.FMI3.CSRun.change_step_total
#audit axioms Rumoca.FMI3.CSRun.Retains.trans
#audit axioms Rumoca.FMI3.CSRun.Retains.suppressed
#audit axioms Rumoca.FMI3.CSRun.advance_retains
#audit axioms Rumoca.FMI3.CSRun.reject_retains
#audit axioms Rumoca.FMI3.CSRun.restart_retains
#audit axioms Rumoca.FMI3.CSRun.Executed.readonly
