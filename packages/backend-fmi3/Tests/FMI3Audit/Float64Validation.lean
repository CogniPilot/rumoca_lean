import RumocaFMI3.Float64Validation
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.Float64Validation.

#audit axioms Rumoca.FMI3.Float64Calls.counter_reference_eval
#audit axioms Rumoca.FMI3.Float64Calls.validation_prefix
#audit axioms Rumoca.FMI3.Float64Calls.validation_reaches
#audit axioms Rumoca.FMI3.Float64Calls.validation_rejects
#audit axioms Rumoca.FMI3.Float64Calls.reference_cases
