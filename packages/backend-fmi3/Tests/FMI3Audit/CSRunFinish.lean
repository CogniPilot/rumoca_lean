import RumocaFMI3.CSRunFinish
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.CSRunFinish.

#audit axioms Rumoca.FMI3.CSRun.query_rehandle
#audit axioms Rumoca.FMI3.CSRun.Change.rehandle
#audit axioms Rumoca.FMI3.CSRun.ReferenceTrace.rehandle
#audit axioms Rumoca.FMI3.CSRun.Change.can_finish
#audit axioms Rumoca.FMI3.CSRun.ReferenceTrace.can_finish
#audit axioms Rumoca.FMI3.CSRun.Stored.mode_cell
#audit axioms Rumoca.FMI3.CSRun.finish_correct
