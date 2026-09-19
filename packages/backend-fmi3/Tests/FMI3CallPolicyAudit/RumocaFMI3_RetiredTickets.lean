import RumocaFMI3.RetiredTickets
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.RetiredTickets.

#audit axioms Rumoca.FMI3.InstanceAuthority.NoTicket.clear
#audit axioms Rumoca.FMI3.InstanceAuthority.NoTicket.completeUse
#audit axioms Rumoca.FMI3.InstanceAuthority.NoTicket.enter
#audit axioms Rumoca.FMI3.InstanceAuthority.NoTicket.publish
#audit axioms Rumoca.FMI3.InstanceAuthority.cleared_no_ticket
#audit axioms Rumoca.FMI3.InstanceAuthority.complete_without_ticket
#audit axioms Rumoca.FMI3.InstanceAuthority.null_release_no_ticket
