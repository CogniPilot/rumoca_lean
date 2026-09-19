import RumocaFMI3.PublicationState
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.PublicationState.

#audit axioms Rumoca.FMI3.PublicationRegistry.publish_origin
#audit axioms Rumoca.FMI3.PublicationRegistry.publish_owned
#audit axioms Rumoca.FMI3.PublicationRegistry.publish_wrong_lease
#audit axioms Rumoca.FMI3.PublicationRegistry.reservations_publish
#audit axioms Rumoca.FMI3.PublicationRegistry.reservations_synchronize
#audit axioms Rumoca.FMI3.PublicationRegistry.synchronize_cleared
#audit axioms Rumoca.FMI3.PublicationRegistry.synchronize_new
#audit axioms Rumoca.FMI3.PublicationRegistry.synchronize_published
#audit axioms Rumoca.FMI3.PublicationRegistry.synchronize_reservations
