import RumocaFMI3.PrivateWriteFrame
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.PrivateWriteFrame.

#audit axioms Rumoca.FMI3.InstanceAuthority.concurrent_preserves_private
#audit axioms Rumoca.FMI3.InstanceAuthority.event_preserves_private
#audit axioms Rumoca.FMI3.InstanceAuthority.internal_preserves_private
#audit axioms Rumoca.FMI3.InstanceAuthority.owned_writes_avoid_private
#audit axioms Rumoca.FMI3.InstanceAuthority.private_record_separate
#audit axioms Rumoca.FMI3.InstanceAuthority.store_preserves_private
