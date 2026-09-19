import RumocaC.InitializationProgress
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.InitializationProgress.

#audit axioms Rumoca.CCalls.InitializationRegion.CompleteReady.zero_iff_halted
#audit axioms Rumoca.CCalls.InitializationRegion.complete_next_ready
#audit axioms Rumoca.CCalls.InitializationRegion.complete_step_decreases
#audit axioms Rumoca.CCalls.InitializationRegion.complete_step_frame
