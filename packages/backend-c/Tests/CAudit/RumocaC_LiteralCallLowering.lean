import RumocaC.LiteralCallLowering
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.LiteralCallLowering.

#audit axioms Rumoca.CLiteral.Lowering.callOperand_lowered
#audit axioms Rumoca.CLiteral.Lowering.parameter_bindings
#audit axioms Rumoca.CLiteral.Lowering.enterCall_lowered
#audit axioms Rumoca.CLiteral.Lowering.resume_lowered
#audit axioms Rumoca.CLiteral.Lowering.next_lowered
#audit axioms Rumoca.CLiteral.Lowering.next_safe
#audit axioms Rumoca.CLiteral.Lowering.call_behaviors
#audit axioms Rumoca.CLiteral.Lowering.invocation_behaviors
#audit axioms Rumoca.CLiteral.Lowering.nextWith_lowered
#audit axioms Rumoca.CLiteral.Lowering.nextWith_safe
