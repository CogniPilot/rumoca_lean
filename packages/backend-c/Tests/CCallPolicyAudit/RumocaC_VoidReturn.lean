import RumocaC.VoidReturn
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.VoidReturn.

#audit axioms Rumoca.CCalls.VoidReturn.Ready.halted_value
#audit axioms Rumoca.CCalls.VoidReturn.Ready.withHeap
#audit axioms Rumoca.CCalls.VoidReturn.Ready.zero_iff_halted
#audit axioms Rumoca.CCalls.VoidReturn.history_ready
#audit axioms Rumoca.CCalls.VoidReturn.next_ready
#audit axioms Rumoca.CCalls.VoidReturn.observed_void
#audit axioms Rumoca.CCalls.VoidReturn.step_ready
