import RumocaFMI3.DerivativeMetadata
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.DerivativeMetadata.

#audit axioms Rumoca.FMI3.DerivativeMetadata.EntryName.unique
#audit axioms Rumoca.FMI3.DerivativeMetadata.DerivativeReference.unique
#audit axioms Rumoca.FMI3.DerivativeMetadata.OrderedDerivatives.unique
#audit axioms Rumoca.FMI3.DerivativeMetadata.OrderedDerivatives.states
#audit axioms Rumoca.FMI3.DerivativeMetadata.described_derivatives
#audit axioms Rumoca.FMI3.DerivativeMetadata.artifact_derivatives
