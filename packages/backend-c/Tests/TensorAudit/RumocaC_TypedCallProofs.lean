import RumocaC.TypedCallProofs
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.TypedCallProofs.

#audit axioms Rumoca.CCalls.Typed.enter_loop_call
#audit axioms Rumoca.CCalls.Typed.loop_step
#audit axioms Rumoca.CCalls.Typed.loop_reaches
#audit axioms Rumoca.CCalls.Typed.loop_behaviors
#audit axioms Rumoca.CCalls.Typed.enter_append
#audit axioms Rumoca.CCalls.Typed.resume_append
#audit axioms Rumoca.CCalls.Typed.append_step
#audit axioms Rumoca.CCalls.Typed.append_reaches
#audit axioms Rumoca.CCalls.Typed.loop_call_reaches
#audit axioms Rumoca.CCalls.Typed.body_step
#audit axioms Rumoca.CCalls.Typed.body_reaches
#audit axioms Rumoca.CCalls.Typed.kernel_step
#audit axioms Rumoca.CCalls.Typed.kernel_reaches
#audit axioms Rumoca.CCalls.Typed.tree_entry
#audit axioms Rumoca.CCalls.Typed.loop_terminates_reaches
#audit axioms Rumoca.CCalls.Typed.loop_terminates_context
#audit axioms Rumoca.CCalls.Typed.loop_call_result
#audit axioms Rumoca.CCalls.Typed.invoke_step
#audit axioms Rumoca.CCalls.Typed.invoke_reaches
#audit axioms Rumoca.CCalls.Typed.invoke_return_reaches
