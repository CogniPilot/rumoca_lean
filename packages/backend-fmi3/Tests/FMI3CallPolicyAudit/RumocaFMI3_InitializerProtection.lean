import RumocaFMI3.InitializerProtection
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.InitializerProtection.

#audit axioms Rumoca.FMI3.PublicationRegistry.reserved_records_separate
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.Ready.destination
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.Ready.foreign_frame
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.step_preserves_other_private
