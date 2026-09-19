import RumocaFMI3.InitializationProtocolInterrupted
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.InitializationProtocolInterrupted.

#audit axioms Rumoca.FMI3.InitializationProtocol.Completed.stopped
#audit axioms Rumoca.FMI3.InitializationProtocol.Interrupted.stopped
#audit axioms Rumoca.FMI3.InitializationProtocol.Stopped.interrupted
#audit axioms Rumoca.FMI3.InitializationProtocol.interrupted_iff
#audit axioms Rumoca.FMI3.InitializationProtocol.ReferenceTrace.split
