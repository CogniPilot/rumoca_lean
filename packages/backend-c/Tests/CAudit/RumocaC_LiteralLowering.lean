import RumocaC.LiteralLowering
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.LiteralLowering.

#audit axioms Rumoca.CLiteral.Lowering.expression_correct
#audit axioms Rumoca.CLiteral.Lowering.arguments_correct
#audit axioms Rumoca.CLiteral.Lowering.body_next
#audit axioms Rumoca.CLiteral.Lowering.body_run
#audit axioms Rumoca.CLiteral.Lowering.body_terminates
#audit axioms Rumoca.CLiteral.Lowering.body_behaviors
#audit axioms Rumoca.CLiteral.Lowering.expression_zeroLiteral

#audit axioms Rumoca.CLiteral.Lowering.Bound.bind
#audit axioms Rumoca.CLiteral.Lowering.bodyBisimulation
#audit axioms Rumoca.CLiteral.Lowering.body_safe_next
#audit axioms Rumoca.CLiteral.Lowering.intrinsic_iff
