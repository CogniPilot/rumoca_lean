import RumocaFMI3.MEFailureMemory
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.MEFailureMemory.

#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.failed
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.failed_reset
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.failed_atomic
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.framed
#audit axioms Rumoca.FMI3.MENumericalHistory.Frame.reset_storage
#audit axioms Rumoca.FMI3.MEFailure.ProtectedFrame.numerical
#audit axioms Rumoca.FMI3.MEFailure.ProtectedFrame.owners
#audit axioms Rumoca.FMI3.MEFailure.Respects.returned
