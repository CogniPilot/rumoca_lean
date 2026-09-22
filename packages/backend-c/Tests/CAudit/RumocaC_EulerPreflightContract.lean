import RumocaC.EulerPreflightContract
import ProofAudit.Audit

-- Audit the complete dependency closure of the module's exported roots.

#audit axioms Rumoca.CEulerPreflight.acceptance_iff_prefix
#audit axioms Rumoca.CEulerPreflight.rejection_iff_overflow
#audit axioms Rumoca.CEulerPreflight.artifact_correct
