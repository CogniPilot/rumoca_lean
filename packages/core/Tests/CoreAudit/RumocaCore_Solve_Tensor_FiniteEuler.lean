import RumocaCore.Solve.Tensor.FiniteEuler
import ProofAudit.Audit

-- Audit the complete dependency closure of the module's exported roots.

#audit axioms Rumoca.Solve.TensorFiniteEuler.trajectory_get
#audit axioms Rumoca.Solve.TensorFiniteEuler.prefix_iff_coordinates
#audit axioms Rumoca.Solve.TensorFiniteEuler.prefix_iff_trajectory
#audit axioms Rumoca.Solve.TensorFiniteEuler.prefix_unique
#audit axioms Rumoca.Solve.TensorFiniteEuler.prefix_exists_iff
#audit axioms Rumoca.Solve.TensorFiniteEuler.failure_iff
#audit axioms Rumoca.Solve.TensorFiniteEuler.total_outcomes
#audit axioms Rumoca.Solve.TensorFiniteEuler.failure_boundary
#audit axioms Rumoca.Solve.TensorFiniteEuler.prefix_iff_path
#audit axioms Rumoca.Solve.TensorFiniteEuler.zero_steps
#audit axioms Rumoca.Solve.TensorFiniteEuler.empty_interval
