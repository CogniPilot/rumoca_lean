import RumocaFMI3.MENumericalRestart
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.MENumericalRestart.

#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.reset_storage
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.stop_outside
#audit axioms Rumoca.FMI3.MENumericalHistory.step_reset_storage
#audit axioms Rumoca.FMI3.MENumericalHistory.CallerStorage.reset
#audit axioms Rumoca.FMI3.MENumericalHistory.reset_state_cell
#audit axioms Rumoca.FMI3.MENumericalHistory.initialized_reset_storage
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.restart
#audit axioms Rumoca.FMI3.MENumericalHistory.restart_atomic
