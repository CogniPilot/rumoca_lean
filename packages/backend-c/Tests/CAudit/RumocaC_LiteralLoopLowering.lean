import RumocaC.LiteralLoopLowering
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.LiteralLoopLowering.

#audit axioms Rumoca.CLiteral.Lowering.loop_expression_correct
#audit axioms Rumoca.CLiteral.Lowering.noDeclarations_lowered
#audit axioms Rumoca.CLiteral.Lowering.loop_safe_next
#audit axioms Rumoca.CLiteral.Lowering.loop_next
#audit axioms Rumoca.CLiteral.Lowering.loop_behaviors
