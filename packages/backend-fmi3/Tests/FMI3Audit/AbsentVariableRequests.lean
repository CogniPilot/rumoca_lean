import RumocaFMI3.AbsentVariableRequests
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.AbsentVariableRequests.

#audit axioms Rumoca.FMI3.AbsentVariables.classify_correct
#audit axioms Rumoca.FMI3.AbsentVariables.classify_call
#audit axioms Rumoca.FMI3.AbsentVariables.request_coverage
#audit axioms Rumoca.FMI3.AbsentVariables.terminated_setter
#audit axioms Rumoca.FMI3.AbsentVariables.cs_step_empty
