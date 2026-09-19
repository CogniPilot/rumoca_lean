import RumocaFMI3.PublicationTransitions
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.PublicationTransitions.

#audit axioms Rumoca.FMI3.PublicationRegistry.advance_claim_free
#audit axioms Rumoca.FMI3.PublicationRegistry.advance_clear
#audit axioms Rumoca.FMI3.PublicationRegistry.advance_void_completion
#audit axioms Rumoca.FMI3.PublicationRegistry.observe_owned
#audit axioms Rumoca.FMI3.PublicationRegistry.synchronize_claim_busy
#audit axioms Rumoca.FMI3.PublicationRegistry.synchronize_claim_free
#audit axioms Rumoca.FMI3.PublicationRegistry.synchronize_clear
