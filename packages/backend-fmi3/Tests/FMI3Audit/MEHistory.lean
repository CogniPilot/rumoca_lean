import RumocaFMI3.MEHistory
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.MEHistory.

#audit axioms Rumoca.FMI3.MEHistory.Buffers.writable
#audit axioms Rumoca.FMI3.MEHistory.Buffers.transport
#audit axioms Rumoca.FMI3.MEHistory.Buffers.Outside.field
#audit axioms Rumoca.FMI3.MEHistory.Buffers.zero
#audit axioms Rumoca.FMI3.MEHistory.Buffers.completed
#audit axioms Rumoca.FMI3.MEHistory.Buffers.discrete
#audit axioms Rumoca.FMI3.MEHistory.step
#audit axioms Rumoca.FMI3.MEHistory.trace
#audit axioms Rumoca.FMI3.MEHistory.continuous_requires_iteration
#audit axioms Rumoca.FMI3.MEHistory.initial_requires_iteration
#audit axioms Rumoca.FMI3.MEHistory.action_frame
#audit axioms Rumoca.FMI3.MEHistory.trace_frame
#audit axioms Rumoca.FMI3.MEHistory.evaluation_preserves_iteration
#audit axioms Rumoca.FMI3.MEHistory.initial_evaluation_still_requires_iteration
