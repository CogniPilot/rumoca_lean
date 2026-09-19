import RumocaCore.Transition.Events.Prefix
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaCore.Transition.Events.Prefix.

#audit axioms Rumoca.Transition.Events.Prefix.trans
#audit axioms Rumoca.Transition.Events.Prefix.forced
#audit axioms Rumoca.Transition.Events.Prefix.terminates_iff
#audit axioms Rumoca.Transition.Events.Prefix.wrong_iff
#audit axioms Rumoca.Transition.Events.Prefix.no_divergence
#audit axioms Rumoca.Transition.Events.Prefix.finite_behaviors
#audit axioms Rumoca.Transition.Events.Prefix.silent_finite_behaviors
