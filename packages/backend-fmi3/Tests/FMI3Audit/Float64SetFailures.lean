import RumocaFMI3.Float64SetFailures
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.Float64SetFailures.

#audit axioms Rumoca.FMI3.Float64Set.entry_cases
#audit axioms Rumoca.FMI3.Float64Set.query_cases
#audit axioms Rumoca.FMI3.Float64Set.failure_unique
#audit axioms Rumoca.FMI3.Float64Set.lifecycle_site
#audit axioms Rumoca.FMI3.Float64Set.array_site
#audit axioms Rumoca.FMI3.Float64Set.entry_site
#audit axioms Rumoca.FMI3.Float64Set.failure_site
#audit axioms Rumoca.FMI3.Float64Set.empty_lifecycle_site
