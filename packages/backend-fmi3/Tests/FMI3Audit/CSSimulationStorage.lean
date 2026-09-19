import RumocaFMI3.CSSimulationStorage
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.CSSimulationStorage.

#audit axioms Rumoca.FMI3.StepEntry.output_storage
#audit axioms Rumoca.FMI3.StepAdvance.written_storage
#audit axioms Rumoca.FMI3.CSRun.advance_storage
#audit axioms Rumoca.FMI3.StepRejections.after_storage
