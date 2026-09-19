import RumocaCore.Transition.Events
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaCore.Transition.Events.

#audit axioms Rumoca.Transition.Events.Reaches.trans
#audit axioms Rumoca.Transition.Events.Reaches.invariant
#audit axioms Rumoca.Transition.Events.Reaches.erases
#audit axioms Rumoca.Transition.Events.quiet_reaches
#audit axioms Rumoca.Transition.Events.quiet_reflects
#audit axioms Rumoca.Transition.Events.accumulate_silent
#audit axioms Rumoca.Transition.Events.records_silent
#audit axioms Rumoca.Transition.Events.quiet_behaviors
#audit axioms Rumoca.Transition.Events.quiet_all
#audit axioms Rumoca.Transition.Events.Forced.reaches
#audit axioms Rumoca.Transition.Events.Forced.accessible
#audit axioms Rumoca.Transition.Events.Forced.terminal_matches
#audit axioms Rumoca.Transition.Events.Forced.behaviors
#audit axioms Rumoca.Transition.Events.no_infinite_of_acc
