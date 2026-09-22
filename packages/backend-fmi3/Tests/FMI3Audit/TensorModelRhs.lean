import RumocaFMI3.TensorModelRhs
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.TensorModelRhs.

#audit axioms Rumoca.FMI3.TensorModelRhs.reaches
#audit axioms Rumoca.FMI3.TensorModelRhs.behaviors
#audit axioms Rumoca.FMI3.TensorModelRhs.events_reaches
#audit axioms Rumoca.FMI3.TensorModelRhs.rendered_contract

-- Canonical dependency-restricted roots; all legacy roots retained.
#audit axioms Rumoca.FMI3.TensorModelRhs.reaches_for
#audit axioms Rumoca.FMI3.TensorModelRhs.behaviors_for
#audit axioms Rumoca.FMI3.TensorModelRhs.events_reaches_for
#audit axioms Rumoca.FMI3.TensorModelRhs.rendered_contract_for
#audit axioms Rumoca.FMI3.TensorModelRhs.FunctionContractFor.to_full
