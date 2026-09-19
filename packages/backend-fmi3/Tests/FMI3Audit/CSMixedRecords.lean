import RumocaFMI3.CSMixedRecords
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.CSMixedRecords.

#audit axioms Rumoca.FMI3.CSMixedRun.ActionContract.run_recorded
#audit axioms Rumoca.FMI3.CSMixedRun.Completed.records
#audit axioms Rumoca.FMI3.CSMixedRun.Performed.records
#audit axioms Rumoca.FMI3.CSMixedRun.Recorded.completed
#audit axioms Rumoca.FMI3.CSMixedRun.RecordedAction.performed
#audit axioms Rumoca.FMI3.CSMixedRun.recorded_iff
