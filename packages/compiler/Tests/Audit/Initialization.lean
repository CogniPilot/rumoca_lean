import Rumoca.Initialization
import ProofAudit.Audit

-- Axiom audit for the roots defined in Rumoca.Initialization.

#audit axioms Rumoca.Source.initializes_iff
#audit axioms Rumoca.Flat.Model.initialization_matches
#audit axioms Rumoca.DAE.Model.initialization_matches
#audit axioms Rumoca.Solve.Model.initialization_checked_real
#audit axioms Rumoca.Solve.Model.initialization_correct
#audit axioms Rumoca.Solve.Model.initialized_solution_unique
#audit axioms Rumoca.Solve.FMI3Model.initialization_matches
#audit axioms Rumoca.GALEC.initialization_matches
