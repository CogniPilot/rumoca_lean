import RumocaFMI3.MEProtocolInterrupted
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.MEProtocolInterrupted.

#audit axioms Rumoca.FMI3.MEProtocol.Interrupted.stopped
#audit axioms Rumoca.FMI3.MEProtocol.Stopped.interrupted
#audit axioms Rumoca.FMI3.MEProtocol.interrupted_iff
