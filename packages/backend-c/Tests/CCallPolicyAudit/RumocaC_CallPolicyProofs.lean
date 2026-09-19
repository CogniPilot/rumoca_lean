import RumocaC.CallPolicyProofs
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.CallPolicyProofs.

#audit axioms Rumoca.CCallPolicy.expression_calls_complete
#audit axioms Rumoca.CCallPolicy.statement_calls_complete
#audit axioms Rumoca.CCallPolicy.checkExpression_correct
#audit axioms Rumoca.CCallPolicy.checkStatement_correct
#audit axioms Rumoca.CCallPolicy.checkFunction_correct
#audit axioms Rumoca.CCallPolicy.checkFunction_inventory
#audit axioms Rumoca.CCallPolicy.checked_operand
#audit axioms Rumoca.CCallPolicy.named_origin
#audit axioms Rumoca.CCallPolicy.checked_named_target
#audit axioms Rumoca.CCallPolicy.loop_ready_next
#audit axioms Rumoca.CCallPolicy.loop_ready_reaches
#audit axioms Rumoca.CCallPolicy.rank_callee_correct
#audit axioms Rumoca.CCallPolicy.check_rank_correct
#audit axioms Rumoca.CCallPolicy.check_ranks_correct
#audit axioms Rumoca.CCallPolicy.program_edge_decreases
#audit axioms Rumoca.CCallPolicy.program_no_cycle
#audit axioms Rumoca.CCallPolicy.kernel_no_call
#audit axioms Rumoca.CCallPolicy.function_inventory_ready
#audit axioms Rumoca.CCallPolicy.resolved_named_edge
