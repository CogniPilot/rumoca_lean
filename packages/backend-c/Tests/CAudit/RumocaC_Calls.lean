import RumocaC.Calls
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.Calls.

#audit axioms Rumoca.CCalls.finiteValue_finite
#audit axioms Rumoca.CCalls.counterValue_counter
#audit axioms Rumoca.CCalls.cast_counter
#audit axioms Rumoca.CCalls.tree_entry
#audit axioms Rumoca.CCalls.run_reaches
#audit axioms Rumoca.CCalls.behaviors_of_run
#audit axioms Rumoca.CCalls.body_step
#audit axioms Rumoca.CCalls.body_reaches
#audit axioms Rumoca.CCalls.body_behaviors
#audit axioms Rumoca.CCalls.kernel_step
#audit axioms Rumoca.CCalls.kernel_reaches
#audit axioms Rumoca.CCalls.kernel_correct
#audit axioms Rumoca.CCalls.body_behaviors_of_reaches
