import RumocaFMI3.InitializationProtocolStorage
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.InitializationProtocolStorage.

#audit axioms Rumoca.FMI3.InitializationProtocol.Setup.entered
#audit axioms Rumoca.FMI3.InitializationProtocol.Setup.framed
#audit axioms Rumoca.FMI3.InitializationProtocol.Phase.Configured.framed
#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.entry
#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.access
#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.entered
#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.exited
#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.reset_done
#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.rejected
#audit axioms Rumoca.FMI3.InitializationProtocol.CallerStorage.refl
#audit axioms Rumoca.FMI3.InitializationProtocol.CallerStorage.trans
#audit axioms Rumoca.FMI3.InitializationProtocol.CallerStorage.ordinary
#audit axioms Rumoca.FMI3.InitializationProtocol.CallerStorage.request
