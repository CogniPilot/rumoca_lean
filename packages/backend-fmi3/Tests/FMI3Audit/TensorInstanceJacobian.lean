import RumocaFMI3.TensorInstanceJacobian
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.TensorInstanceJacobian.

#audit axioms Rumoca.FMI3.TensorInstanceJacobian.jacobian_writes_events

-- Canonical dependency-restricted roots; all legacy roots retained.
#audit axioms Rumoca.FMI3.TensorInstanceJacobian.jacobian_writes_events_for
