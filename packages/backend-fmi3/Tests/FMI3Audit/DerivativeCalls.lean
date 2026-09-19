import RumocaFMI3.DerivativeCalls
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.DerivativeCalls.

#audit axioms Rumoca.FMI3.DerivativeCalls.parameters_bound
#audit axioms Rumoca.FMI3.DerivativeCalls.body_eq
#audit axioms Rumoca.FMI3.DerivativeCalls.accepted_run
#audit axioms Rumoca.FMI3.DerivativeCalls.enter_rhs
#audit axioms Rumoca.FMI3.DerivativeCalls.return_rhs
#audit axioms Rumoca.FMI3.DerivativeCalls.finish
#audit axioms Rumoca.FMI3.DerivativeCalls.reaches
#audit axioms Rumoca.FMI3.DerivativeCalls.behaviors
