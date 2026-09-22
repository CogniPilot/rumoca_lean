import RumocaC.LiteralPoolStorage
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.LiteralPoolStorage.

#audit axioms Rumoca.CLiteral.Pool.blocks_unique
#audit axioms Rumoca.CLiteral.Pool.installed
#audit axioms Rumoca.CLiteral.Pool.storage_valid
#audit axioms Rumoca.CLiteral.Pool.install_load
#audit axioms Rumoca.CLiteral.Pool.install_existing
#audit axioms Rumoca.CLiteral.Pool.install_preserves
#audit axioms Rumoca.CLiteral.Pool.globalBindings
#audit axioms Rumoca.CLiteral.Pool.reserved_agreement
#audit axioms Rumoca.CLiteral.Pool.storage_after_steps

#audit axioms Rumoca.CLiteral.Pool.HeaderFresh
#audit axioms Rumoca.CLiteral.Pool.install
#audit axioms Rumoca.CLiteral.Pool.install_frame
#audit axioms Rumoca.CLiteral.Pool.interface
#audit axioms Rumoca.CLiteral.Pool.namedInterface
