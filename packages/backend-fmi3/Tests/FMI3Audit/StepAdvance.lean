import RumocaFMI3.StepAdvance
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.StepAdvance.

#audit axioms Rumoca.FMI3.StepAdvance.actual_tail
#audit axioms Rumoca.FMI3.StepAdvance.time_ne_state
#audit axioms Rumoca.FMI3.StepAdvance.reaches
#audit axioms Rumoca.FMI3.StepAdvance.written_frame
#audit axioms Rumoca.FMI3.StepAdvance.written_values
