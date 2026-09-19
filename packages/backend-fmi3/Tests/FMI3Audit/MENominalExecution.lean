import RumocaFMI3.MENominalExecution
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.MENominalExecution.

#audit axioms Rumoca.FMI3.MENominalCalls.separate_frame
#audit axioms Rumoca.FMI3.MENominalCalls.Memory.success
#audit axioms Rumoca.FMI3.MENominalCalls.Memory.failure
#audit axioms Rumoca.FMI3.MENominalCalls.Contract.quiet
#audit axioms Rumoca.FMI3.MENominalCalls.execution
