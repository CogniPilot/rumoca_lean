import RumocaFMI3.ResourceHistory
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.ResourceHistory.

#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Step.erases
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.history_erases
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.history_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.history_retired
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.step_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.step_retired
#audit axioms Rumoca.FMI3.InstanceAuthority.idle_call_origins
