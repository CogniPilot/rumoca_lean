import RumocaFMI3.CountQueries
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.CountQueries.

#audit axioms Rumoca.FMI3.CountQueries.body_eq
#audit axioms Rumoca.FMI3.CountQueries.parameters_bound
#audit axioms Rumoca.FMI3.CountQueries.body_run
#audit axioms Rumoca.FMI3.CountQueries.call_reaches
#audit axioms Rumoca.FMI3.CountQueries.call_behaviors
#audit axioms Rumoca.FMI3.CountQueries.frame
#audit axioms Rumoca.FMI3.CountQueries.stored_count
#audit axioms Rumoca.FMI3.CountQueries.null_run
#audit axioms Rumoca.FMI3.CountQueries.null_reaches
#audit axioms Rumoca.FMI3.CountQueries.null_behaviors
#audit axioms Rumoca.FMI3.CountQueries.continuous_count_matches_solve
#audit axioms Rumoca.FMI3.CountQueries.rejected_reaches
#audit axioms Rumoca.FMI3.CountQueries.rejected_behaviors
#audit axioms Rumoca.FMI3.CountQueries.missing_run
#audit axioms Rumoca.FMI3.CountQueries.missing_reaches
#audit axioms Rumoca.FMI3.CountQueries.missing_behaviors
#audit axioms Rumoca.FMI3.CountQueries.function_tokenization
