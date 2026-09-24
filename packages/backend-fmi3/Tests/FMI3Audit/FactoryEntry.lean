import RumocaFMI3.FactoryEntry
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.FactoryEntry.

#audit axioms Rumoca.FMI3.FactoryEntry.coSimulation_guard
#audit axioms Rumoca.FMI3.FactoryEntry.validation_entry

-- Factory pointer migration: retained generic domains and actual typed routes.
#audit axioms Rumoca.FMI3.FactoryEntry.coSimulation_guard_with
#audit axioms Rumoca.FMI3.FactoryEntry.validation_entry_with
#audit axioms Rumoca.FMI3.FactoryPrefix.body
#audit axioms Rumoca.FMI3.FactoryPrefix.bodyWith
#audit axioms Rumoca.FMI3.FactoryPrefix.capabilityGuard
#audit axioms Rumoca.FMI3.FactoryPrefix.capabilityGuardWith
#audit axioms Rumoca.FMI3.FactoryPrefix.entry
#audit axioms Rumoca.FMI3.FactoryPrefix.entryWith
#audit axioms Rumoca.FMI3.FactoryPrefix.identityGuard
#audit axioms Rumoca.FMI3.FactoryPrefix.identityGuardWith
#audit axioms Rumoca.FMI3.FactoryPrefix.logicalBody
#audit axioms Rumoca.FMI3.FactoryPrefix.logicalCapabilityGuard
#audit axioms Rumoca.FMI3.FactoryPrefix.logicalEntry
#audit axioms Rumoca.FMI3.FactoryPrefix.logicalIdentityGuard
