import RumocaFMI3.RuntimeEnvironment
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.RuntimeEnvironment.

#audit axioms Rumoca.FMI3.RuntimeEnvironment.types_agree
#audit axioms Rumoca.FMI3.RuntimeEnvironment.time_body_agrees
#audit axioms Rumoca.FMI3.RuntimeEnvironment.time_call_behaviors
#audit axioms Rumoca.FMI3.RuntimeEnvironment.model_advance_behaviors
#audit axioms Rumoca.FMI3.RuntimeEnvironment.time_quiet
