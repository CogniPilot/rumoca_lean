import RumocaFMI3.CSProtocolInterrupted
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.CSProtocolInterrupted.

#audit axioms Rumoca.FMI3.CSProtocol.Interrupted.stopped
#audit axioms Rumoca.FMI3.CSProtocol.Stopped.interrupted
#audit axioms Rumoca.FMI3.CSProtocol.interrupted_iff
