import RumocaC.Fenv
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.Fenv.

#audit axioms Rumoca.CFenv.Header.nearest_binding
#audit axioms Rumoca.CFenv.Header.other_binding
#audit axioms Rumoca.CFenv.Header.nearest_typed
#audit axioms Rumoca.CFenv.Header.failure_distinct
#audit axioms Rumoca.CFenv.Header.expression_agrees
#audit axioms Rumoca.CFenv.rounding_branch_path
