import RumocaC.CallParameters
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.CallParameters.

#audit axioms Rumoca.CCalls.Parameters.convert_stable
#audit axioms Rumoca.CCalls.Parameters.parameters_typed
#audit axioms Rumoca.CCalls.Parameters.parameters_length
#audit axioms Rumoca.CCalls.Parameters.parameters_unknown

#audit axioms Rumoca.CCalls.Parameters.coherent_bind
#audit axioms Rumoca.CCalls.Parameters.coherent_domain
