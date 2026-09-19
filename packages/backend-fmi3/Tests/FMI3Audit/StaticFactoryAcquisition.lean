import RumocaFMI3.StaticFactoryAcquisition
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.StaticFactoryAcquisition.

#audit axioms Rumoca.FMI3.StaticFactory.public_create_owned
#audit axioms Rumoca.FMI3.SlotOwners.release_reserved_restore
