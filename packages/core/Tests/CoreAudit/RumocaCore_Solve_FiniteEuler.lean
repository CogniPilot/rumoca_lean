import RumocaCore.Solve.FiniteEuler
import ProofAudit.Audit

-- Audit the complete dependency closure of the module's exported roots.

#audit axioms Rumoca.Solve.FiniteEuler.checkedAdd_some_iff
#audit axioms Rumoca.Solve.FiniteEuler.checkedAdd_none_iff
#audit axioms Rumoca.Solve.FiniteEuler.adds_iff_domain
#audit axioms Rumoca.Solve.FiniteEuler.prefix_succ_iff
#audit axioms Rumoca.Solve.FiniteEuler.success_iff
#audit axioms Rumoca.Solve.FiniteEuler.prefix_iff_trajectory
#audit axioms Rumoca.Solve.FiniteEuler.success_iff_trajectory
#audit axioms Rumoca.Solve.FiniteEuler.failure_persists
#audit axioms Rumoca.Solve.FiniteEuler.failure_iff
#audit axioms Rumoca.Solve.FiniteEuler.total_outcomes
#audit axioms Rumoca.Solve.FiniteEuler.outcomes_exclusive
#audit axioms Rumoca.Solve.FiniteEuler.failure_boundary
#audit axioms Rumoca.Solve.FiniteEuler.adds_iff_tensor_result
#audit axioms Rumoca.Solve.FiniteEuler.prefix_of_path
#audit axioms Rumoca.Solve.FiniteEuler.success_iff_path
#audit axioms Rumoca.Solve.FiniteEuler.negative_zero_interval
