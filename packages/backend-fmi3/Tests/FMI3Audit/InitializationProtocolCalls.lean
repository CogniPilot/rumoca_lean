import RumocaFMI3.InitializationProtocolCalls
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.InitializationProtocolCalls.

#audit axioms Rumoca.FMI3.InitializationProtocol.CallContract.quiet
#audit axioms Rumoca.FMI3.InitializationProtocol.Result.ordinary
#audit axioms Rumoca.FMI3.InitializationProtocol.access_call
#audit axioms Rumoca.FMI3.InitializationProtocol.enter_call
#audit axioms Rumoca.FMI3.InitializationProtocol.exit_call
#audit axioms Rumoca.FMI3.InitializationProtocol.reset_call
