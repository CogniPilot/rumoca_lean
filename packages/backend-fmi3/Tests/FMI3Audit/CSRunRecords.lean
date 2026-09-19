import RumocaFMI3.CSRunRecords
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.CSRunRecords.

#audit axioms Rumoca.FMI3.CSRun.RecordedAction.performed
#audit axioms Rumoca.FMI3.CSRun.Performed.records
#audit axioms Rumoca.FMI3.CSRun.Recorded.completed
#audit axioms Rumoca.FMI3.CSRun.Completed.records
#audit axioms Rumoca.FMI3.CSRun.recorded_iff
#audit axioms Rumoca.FMI3.CSRun.RecordedAction.length
#audit axioms Rumoca.FMI3.CSRun.Recorded.length
