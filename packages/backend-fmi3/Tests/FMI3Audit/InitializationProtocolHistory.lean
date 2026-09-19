import RumocaFMI3.InitializationProtocolHistory
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.InitializationProtocolHistory.

#audit axioms Rumoca.FMI3.InitializationProtocol.Invariant.initial
#audit axioms Rumoca.FMI3.InitializationProtocol.Invariant.advance
#audit axioms Rumoca.FMI3.InitializationProtocol.Checkpoints.stored
#audit axioms Rumoca.FMI3.InitializationProtocol.Completed.correct
#audit axioms Rumoca.FMI3.InitializationProtocol.progress
