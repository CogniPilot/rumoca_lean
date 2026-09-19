import RumocaFMI3.StateSetterPolicy
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.StateSetterPolicy.

#audit axioms Rumoca.FMI3.StateSetterPolicy.StateDeclaration.unique
#audit axioms Rumoca.FMI3.StateSetterPolicy.artifact_modes
#audit axioms Rumoca.FMI3.StateSetterPolicy.continuous_state
#audit axioms Rumoca.FMI3.StateSetterPolicy.cs_state_simulation
#audit axioms Rumoca.FMI3.StateSetterPolicy.event_state
#audit axioms Rumoca.FMI3.StateSetterPolicy.writable_declaration
#audit axioms Rumoca.FMI3.StateSetterPolicy.writable_guard
#audit axioms Rumoca.FMI3.StateSetterPolicy.writable_modes
