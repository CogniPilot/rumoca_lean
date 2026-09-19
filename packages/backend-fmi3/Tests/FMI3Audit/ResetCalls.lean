import RumocaFMI3.ResetCalls
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.ResetCalls.

#audit axioms Rumoca.FMI3.Reset.parameters_bound
#audit axioms Rumoca.FMI3.Reset.call_reaches
#audit axioms Rumoca.FMI3.Reset.call_behaviors
#audit axioms Rumoca.FMI3.Reset.null_reaches
#audit axioms Rumoca.FMI3.Reset.null_behaviors
#audit axioms Rumoca.FMI3.Reset.correct
