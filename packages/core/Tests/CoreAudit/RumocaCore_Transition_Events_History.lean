import RumocaCore.Transition.Events.History
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaCore.Transition.Events.History.

#audit axioms Rumoca.Transition.Events.History.ext
#audit axioms Rumoca.Transition.Events.records_unique
#audit axioms Rumoca.Transition.Events.accumulate_prefix
#audit axioms Rumoca.Transition.Events.accumulate_get
#audit axioms Rumoca.Transition.Events.records_exists
#audit axioms Rumoca.Transition.Events.accumulate_drop_silent
#audit axioms Rumoca.Transition.Events.records_drop_silent
