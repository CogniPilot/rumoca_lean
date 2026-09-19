import RumocaFMI3.MEEventIndicatorExecution
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.MEEventIndicatorExecution.

#audit axioms Rumoca.FMI3.MEEventIndicatorCalls.Contract.quiet
#audit axioms Rumoca.FMI3.MEEventIndicatorCalls.Memory.failure
#audit axioms Rumoca.FMI3.MEEventIndicatorCalls.Memory.success
#audit axioms Rumoca.FMI3.MEEventIndicatorCalls.execution
