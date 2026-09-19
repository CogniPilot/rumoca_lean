import RumocaCore.Solve.FMI3OriginProofs
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaCore.Solve.FMI3OriginProofs.

#audit axioms Rumoca.Solve.FMI3Model.source_origin
#audit axioms Rumoca.Solve.FMI3Model.origin_ancestry
#audit axioms Rumoca.Solve.FMI3Model.trace_correct
#audit axioms Rumoca.Solve.FMI3Model.rhs_matches_solve
#audit axioms Rumoca.Solve.FMI3Model.initial_matches_solve
#audit axioms Rumoca.Solve.FMI3Model.output_matches_state
#audit axioms Rumoca.Solve.FMI3Model.preparation_preserves
