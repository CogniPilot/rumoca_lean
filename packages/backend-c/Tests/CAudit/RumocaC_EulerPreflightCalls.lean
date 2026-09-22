import RumocaC.EulerPreflightCalls
import ProofAudit.Audit

-- Audit the complete dependency closure of the module's exported roots.

#audit axioms Rumoca.CEulerPreflight.bind_parameters
#audit axioms Rumoca.CEulerPreflight.bind_types
#audit axioms Rumoca.CEulerPreflight.body_field_free
#audit axioms Rumoca.CEulerPreflight.call_reaches
#audit axioms Rumoca.CEulerPreflight.call_correct
