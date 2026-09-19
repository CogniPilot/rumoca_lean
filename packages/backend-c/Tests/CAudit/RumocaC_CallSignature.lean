import RumocaC.CallSignature
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.CallSignature.

#audit axioms Rumoca.CCalls.Signature.Arguments.length
#audit axioms Rumoca.CCalls.Signature.locals_cons
#audit axioms Rumoca.CCalls.Signature.locals_missing
#audit axioms Rumoca.CCalls.Signature.parameters_bound
#audit axioms Rumoca.CCalls.Signature.call_entry
#audit axioms Rumoca.CCalls.Signature.witness_valid
#audit axioms Rumoca.CCalls.Signature.arguments_exist
