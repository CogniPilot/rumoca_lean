import RumocaFMI3.ModelRhs
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.ModelRhs.

#audit axioms Rumoca.FMI3.ModelRhs.parameters_bound
#audit axioms Rumoca.FMI3.ModelRhs.types_bound
#audit axioms Rumoca.FMI3.ModelRhs.call_numerical
#audit axioms Rumoca.FMI3.ModelRhs.reaches
#audit axioms Rumoca.FMI3.ModelRhs.behaviors
#audit axioms Rumoca.FMI3.ModelRhs.rendered_contract
