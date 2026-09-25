import RumocaFMI3.InitializationProtocolLifetime
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.InitializationProtocolLifetime.

#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.created
#audit axioms Rumoca.FMI3.InitializationProtocol.Phase.can_finish
#audit axioms Rumoca.FMI3.InitializationProtocol.Completed.release
#audit axioms Rumoca.FMI3.InitializationProtocol.freed_correct
#audit axioms Rumoca.FMI3.InitializationProtocol.other_instance
#audit axioms Rumoca.FMI3.InitializationProtocol.untouched_other
