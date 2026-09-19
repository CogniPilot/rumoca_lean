import RumocaFMI3.CallOrigins
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.CallOrigins.

#audit axioms Rumoca.FMI3.InstanceAuthority.CallOrigin.map
#audit axioms Rumoca.FMI3.InstanceAuthority.CallOrigin.retire
#audit axioms Rumoca.FMI3.InstanceAuthority.CallOrigins.arguments
#audit axioms Rumoca.FMI3.InstanceAuthority.clear_call_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.factory_no_ticket
#audit axioms Rumoca.FMI3.InstanceAuthority.publish_call_origins
