import RumocaFMI3.Float64SetEntry
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.Float64SetEntry.

#audit axioms Rumoca.FMI3.Float64Set.body_eq
#audit axioms Rumoca.FMI3.Float64Set.values_eq
#audit axioms Rumoca.FMI3.Float64Set.validation_closed
#audit axioms Rumoca.FMI3.Float64Set.write_closed
#audit axioms Rumoca.FMI3.Float64Set.entry_run
#audit axioms Rumoca.FMI3.Float64Set.guard_run
#audit axioms Rumoca.FMI3.Float64Set.empty_behaviors
#audit axioms Rumoca.FMI3.Float64Set.null_behaviors
