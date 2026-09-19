import RumocaFMI3.ReservationRegistryHistory
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.ReservationRegistryHistory.

#audit axioms Rumoca.FMI3.ReservationRegistry.Step.erases
#audit axioms Rumoca.FMI3.ReservationRegistry.history_erases
#audit axioms Rumoca.FMI3.ReservationRegistry.history_lift
#audit axioms Rumoca.FMI3.ReservationRegistry.history_represents
#audit axioms Rumoca.FMI3.ReservationRegistry.step_represents
