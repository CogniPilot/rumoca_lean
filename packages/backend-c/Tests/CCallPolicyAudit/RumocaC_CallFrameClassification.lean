import RumocaC.CallFrameClassification
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.CallFrameClassification.

#audit axioms Rumoca.CStoreInvariant.ExceptPreserves.mono
#audit axioms Rumoca.CStoreInvariant.concurrent_classifies
#audit axioms Rumoca.CStoreInvariant.event_classifies
#audit axioms Rumoca.CStoreInvariant.linked_except
