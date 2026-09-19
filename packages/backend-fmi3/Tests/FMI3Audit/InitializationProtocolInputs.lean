import RumocaFMI3.InitializationProtocolInputs
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.InitializationProtocolInputs.

#audit axioms Rumoca.FMI3.InitializationProtocol.ReadBank.Frame.refl
#audit axioms Rumoca.FMI3.InitializationProtocol.ReadBank.Frame.trans
#audit axioms Rumoca.FMI3.InitializationProtocol.ReadBank.Stored.framed
#audit axioms Rumoca.FMI3.InitializationProtocol.Result.inputs_framed
#audit axioms Rumoca.FMI3.InitializationProtocol.ReadBank.Stored.not_flag
