import RumocaC.CallPolicyExecution
import RumocaC.CallLinkage
import RumocaC.CallDepth
import RumocaC.CallPolicyProofs
import ProofAudit.Audit

/-! Independently cached formal audits for the call policy; no example-based tests. -/

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

#audit axioms Rumoca.CCallDepth.Frames.depth_bound
#audit axioms Rumoca.CCallDepth.Frames.weaken
#audit axioms Rumoca.CCallDepth.definition_ready
#audit axioms Rumoca.CCallDepth.enter_ready
#audit axioms Rumoca.CCallDepth.event_ready
#audit axioms Rumoca.CCallDepth.execution_depth_bound
#audit axioms Rumoca.CCallDepth.initial_ready
#audit axioms Rumoca.CCallDepth.internal_ready
#audit axioms Rumoca.CCallDepth.reaches_ready
#audit axioms Rumoca.CCallDepth.ready_depth
#audit axioms Rumoca.CCallDepth.resume_ready
#audit axioms Rumoca.CCallPolicy.entered_internal_edge
#audit axioms Rumoca.CCallPolicy.internal_resolution
#audit axioms Rumoca.CCallPolicy.scheduled_internal_decreases
#audit axioms Rumoca.CCallPolicy.scheduled_internal_edge
#audit axioms Rumoca.CCalls.Events.Linkage.withAddress_foreign
#audit axioms Rumoca.CCalls.Events.Linkage.withExternal_bound
#audit axioms Rumoca.CCalls.Events.Linkage.withExternal_foreign
#audit axioms Rumoca.CCalls.Events.Linkage.withExternal_keeps
