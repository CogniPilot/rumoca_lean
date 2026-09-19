import RumocaFMI3.InitializationProtocolRunFrames
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.InitializationProtocolRunFrames.

#audit axioms Rumoca.FMI3.InitializationProtocol.MEOutputsGuarded.protects
#audit axioms Rumoca.FMI3.InitializationProtocol.CSOutputsGuarded.protects
#audit axioms Rumoca.FMI3.InitializationProtocol.Retains.me_configuration
#audit axioms Rumoca.FMI3.InitializationProtocol.Retains.cs
#audit axioms Rumoca.FMI3.InitializationProtocol.Retention.me_created
