import RumocaC.LiteralPoolLowering
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.LiteralPoolLowering.

#audit axioms Rumoca.CLiteral.Pool.statement_safe
#audit axioms Rumoca.CLiteral.collected_names_cover
#audit axioms Rumoca.CLiteral.Pool.program_agrees
#audit axioms Rumoca.CLiteral.Pool.program_safe
#audit axioms Rumoca.CLiteral.Pool.invocation_behaviors
