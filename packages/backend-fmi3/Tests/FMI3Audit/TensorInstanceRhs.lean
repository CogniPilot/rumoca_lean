import RumocaFMI3.TensorInstanceRhs
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.TensorInstanceRhs.

#audit axioms Rumoca.FMI3.TensorInstanceRhs.derivative_valid
#audit axioms Rumoca.FMI3.TensorInstanceRhs.derivativeBuffer_eq
#audit axioms Rumoca.FMI3.TensorInstanceRhs.parameter_bound
#audit axioms Rumoca.FMI3.TensorInstanceRhs.derivative_writes
#audit axioms Rumoca.FMI3.TensorInstanceRhs.buffer_outside
#audit axioms Rumoca.FMI3.TensorInstanceRhs.derivative_writes_events
#audit axioms Rumoca.FMI3.TensorInstanceRhs.field_outside
