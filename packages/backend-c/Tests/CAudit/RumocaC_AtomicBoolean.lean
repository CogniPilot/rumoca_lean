import RumocaC.AtomicBoolean
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.AtomicBoolean.

#audit axioms Rumoca.CAtomicBoolean.read_iff
#audit axioms Rumoca.CAtomicBoolean.exchange_iff
#audit axioms Rumoca.CAtomicBoolean.write_iff
#audit axioms Rumoca.CAtomicBoolean.exchange_same
#audit axioms Rumoca.CAtomicBoolean.ordinary_load_unsupported
#audit axioms Rumoca.CAtomicBoolean.ordinary_store_unsupported
