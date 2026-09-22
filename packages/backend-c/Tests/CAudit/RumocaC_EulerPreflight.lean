import RumocaC.EulerPreflight
import ProofAudit.Audit

-- Audit the complete dependency closure of the module's exported roots.

#audit axioms Rumoca.CEulerPreflight.snapshots_spec
#audit axioms Rumoca.CEulerPreflight.iteration_reaches
#audit axioms Rumoca.CEulerPreflight.segment_reaches
#audit axioms Rumoca.CEulerPreflight.function_correct
