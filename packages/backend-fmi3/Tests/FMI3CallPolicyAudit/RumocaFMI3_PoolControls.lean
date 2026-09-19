import RumocaFMI3.PoolControls
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.PoolControls.

#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.borrowed_writable
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.complete_controls
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.complete_writable_other
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.controls_private
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.exchange_controls
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.initializer_controls
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.invoke_controls
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.invoke_writable_other
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.release_controls
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.writable_excludes_private
#audit axioms Rumoca.FMI3.InstanceAuthority.complete_preserves_ticket
