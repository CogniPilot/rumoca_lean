import RumocaC.AtomicFrame
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.AtomicFrame.

#audit axioms Rumoca.CAtomicBoolean.ordinary_store_preserves
#audit axioms Rumoca.CAtomicBoolean.internal_preserves

#audit axioms Rumoca.CAtomicBoolean.Preserves
#audit axioms Rumoca.CAtomicBoolean.Preserves.refl
#audit axioms Rumoca.CAtomicBoolean.Preserves.trans
#audit axioms Rumoca.CAtomicBoolean.ordinary_stable
