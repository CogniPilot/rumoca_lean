import RumocaFMI3.InitializationProtocolHandoff
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.InitializationProtocolHandoff.

#audit axioms Rumoca.FMI3.InitializationProtocol.CallerStorage.me_outputs
#audit axioms Rumoca.FMI3.InitializationProtocol.CallerStorage.cs_outputs
#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.me_ready
#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.cs_ready
#audit axioms Rumoca.FMI3.InitializationProtocol.Invariant.me_ready
#audit axioms Rumoca.FMI3.InitializationProtocol.Invariant.cs_ready
