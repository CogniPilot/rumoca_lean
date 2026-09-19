import RumocaFMI3.ClaimInitialization
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.ClaimInitialization.

#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.Ready.halted
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.Ready.withHeap
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.step_other_instance
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.step_ready
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.step_with_frame
