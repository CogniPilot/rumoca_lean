import RumocaFMI3.MESimulationStorage
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.MESimulationStorage.

#audit axioms Rumoca.FMI3.HistoryProofs.write_storage
#audit axioms Rumoca.FMI3.HistoryProofs.raise_storage
#audit axioms Rumoca.FMI3.HistoryProofs.event_storage
#audit axioms Rumoca.FMI3.HistoryProofs.completed_storage
#audit axioms Rumoca.FMI3.MEHistory.action_storage
#audit axioms Rumoca.FMI3.MENumericalHistory.action_storage
#audit axioms Rumoca.FMI3.MENumericalHistory.restart_storage
#audit axioms Rumoca.FMI3.MEFailure.Prepares.storage
