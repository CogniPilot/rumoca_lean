import RumocaC.TypedEventsTransfer
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.TypedEventsTransfer.

#audit axioms Rumoca.CCalls.Events.enter_loop_call_events
#audit axioms Rumoca.CCalls.Events.loop_step_events
#audit axioms Rumoca.CCalls.Events.loop_reaches_events
#audit axioms Rumoca.CCalls.Events.loop_terminates_reaches_events
#audit axioms Rumoca.CCalls.Events.enter_append_events
#audit axioms Rumoca.CCalls.Events.append_step_events
#audit axioms Rumoca.CCalls.Events.append_reaches_events
#audit axioms Rumoca.CCalls.Events.loop_call_reaches_events
#audit axioms Rumoca.CCalls.Events.loop_call_behaviors_events
