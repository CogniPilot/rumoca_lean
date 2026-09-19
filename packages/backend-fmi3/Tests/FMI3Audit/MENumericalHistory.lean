import RumocaFMI3.MENumericalHistory
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.MENumericalHistory.

#audit axioms Rumoca.FMI3.MENumericalHistory.Action.prepare_correct
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.mode_loaded
#audit axioms Rumoca.FMI3.MENumericalHistory.Action.frame
#audit axioms Rumoca.FMI3.MENumericalHistory.step
#audit axioms Rumoca.FMI3.MENumericalHistory.Action.Prepares.unique
#audit axioms Rumoca.FMI3.MENumericalHistory.Action.Observes.unique
#audit axioms Rumoca.FMI3.MENumericalHistory.trace
#audit axioms Rumoca.FMI3.MENumericalHistory.Calls.executes
#audit axioms Rumoca.FMI3.MENumericalHistory.Calls.determines
