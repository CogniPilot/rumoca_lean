import RumocaC.LiteralEventLowering
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.LiteralEventLowering.

#audit axioms Rumoca.CLiteral.Lowering.Events.target_lowered
#audit axioms Rumoca.CLiteral.Lowering.Events.resolve_lowered
#audit axioms Rumoca.CLiteral.Lowering.Events.operand_lowered
#audit axioms Rumoca.CLiteral.Lowering.Events.operand_head_safe
#audit axioms Rumoca.CLiteral.Lowering.Events.enter_lowered
#audit axioms Rumoca.CLiteral.Lowering.Events.operand_fresh
#audit axioms Rumoca.CLiteral.Lowering.Events.enter_safe
#audit axioms Rumoca.CLiteral.Lowering.Events.internal_lowered
#audit axioms Rumoca.CLiteral.Lowering.Events.internal_safe
#audit axioms Rumoca.CLiteral.Lowering.Events.step_safe
#audit axioms Rumoca.CLiteral.Lowering.Events.step_lowered
#audit axioms Rumoca.CLiteral.Lowering.Events.internal_reflected
#audit axioms Rumoca.CLiteral.Lowering.Events.step_reflected
#audit axioms Rumoca.CLiteral.Lowering.Events.behaviors
#audit axioms Rumoca.CLiteral.Lowering.Events.invocation_behaviors

#audit axioms Rumoca.CLiteral.Lowering.Events.bisimulation
#audit axioms Rumoca.CLiteral.Lowering.Events.program
