import Rumoca.Behavioral
import ProofAudit.Audit

-- Axiom audit for the roots defined in Rumoca.Behavioral.

#audit axioms Rumoca.Source.solution_unique
#audit axioms Rumoca.Solve.lower_samples_correct
#audit axioms Rumoca.CStatements.lower_behavior_correct
#audit axioms Rumoca.CStatements.real_refinement
#audit axioms Rumoca.Flat.behavior_correct
#audit axioms Rumoca.DAE.behavior_correct
#audit axioms Rumoca.Solve.behavior_correct
#audit axioms Rumoca.CStatements.solve_behavior_correct
#audit axioms Rumoca.lowering_chain_behavior_correct
#audit axioms Rumoca.CStatements.model_exchange_correct
#audit axioms Rumoca.CStatements.co_simulation_correct
