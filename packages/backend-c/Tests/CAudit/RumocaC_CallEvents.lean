import RumocaC.CallEvents
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.CallEvents.

#audit axioms Rumoca.CCalls.Events.enter_preserves
#audit axioms Rumoca.CCalls.Events.internal_preserves
#audit axioms Rumoca.CCalls.Events.step_preserves
#audit axioms Rumoca.CCalls.Events.reaches_preserves
#audit axioms Rumoca.CCalls.Events.termination_preserves
#audit axioms Rumoca.CCalls.Events.external_entry_exclusive
#audit axioms Rumoca.CCalls.Events.external_reaches
#audit axioms Rumoca.CCalls.Events.internal_unique
#audit axioms Rumoca.CCalls.Events.body_step
#audit axioms Rumoca.CCalls.Events.body_reaches
#audit axioms Rumoca.CCalls.Events.internal_prefix
#audit axioms Rumoca.CCalls.Events.tree_entry
#audit axioms Rumoca.CCalls.Events.external_prefix
#audit axioms Rumoca.CCalls.Events.return_forced
#audit axioms Rumoca.CCalls.Events.external_behaviors
