import RumocaFMI3.Float64History
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.Float64History.

#audit axioms Rumoca.FMI3.Float64Access.Request.readback_correct
#audit axioms Rumoca.FMI3.Float64Access.trace
#audit axioms Rumoca.FMI3.Float64Access.Calls.executes
#audit axioms Rumoca.FMI3.Float64Access.Calls.determines
#audit axioms Rumoca.FMI3.Float64Access.Calls.execution_iff
