import RumocaFMI3.StateMetadata
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.StateMetadata.

#audit axioms Rumoca.FMI3.StateMetadata.StateReference.unique
#audit axioms Rumoca.FMI3.StateMetadata.OrderedStates.unique
#audit axioms Rumoca.FMI3.StateMetadata.described_states
#audit axioms Rumoca.FMI3.StateMetadata.artifact_states
