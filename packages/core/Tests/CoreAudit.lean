import RumocaCore.GALEC.Protocol
import RumocaCore.GALEC.UnitProfile
import RumocaCore.Solve.AlgorithmProofs
import RumocaCore.GALEC.Semantics
import ProofAudit.Audit
import RumocaCore.Driven.IR
import RumocaCore.Driven.Lowering
import RumocaCore.FMI3.History
import RumocaCore.FMI3.Initialization
import RumocaCore.FMI3.Lifecycle
import RumocaCore.FMI3.Time
import RumocaCore.Transition.Prefix
import RumocaCore.Transition.Simulation
import RumocaCore.Pass
import RumocaCore.Profile
import RumocaCore.Real.Binary64
import RumocaCore.Real.Comparison
import RumocaCore.Real.Encoding
import RumocaCore.Solve.FMI3
import RumocaCore.Solve.IVP
import RumocaCore.Solve.ModelData
import RumocaCore.Solve.ModelExchange
import RumocaCore.Solve.Tensor
import RumocaCore.Tensor.Matrix
import RumocaCore.Transition
import RumocaCore.Initialization.Real
import RumocaCore.Initialization.DiagnosticProofs
import RumocaCore.Provenance.Lowering

#audit axioms Rumoca.Provenance.Context.source_fields
#audit axioms Rumoca.Provenance.Context.lookup
#audit axioms Rumoca.Flat.Model.derivative_source
#audit axioms Rumoca.Flat.Model.literal_source
#audit axioms Rumoca.Flat.Model.initialization_origin
#audit axioms Rumoca.DAE.Model.residual_ancestry
#audit axioms Rumoca.DAE.Model.initialization_origin
#audit axioms Rumoca.Solve.Model.initial_ancestry
#audit axioms Rumoca.Solve.Model.completion_ancestry
#audit axioms Rumoca.Solve.Model.notice_ancestry
#audit axioms Rumoca.Solve.Model.derivative_ancestry
#audit axioms Rumoca.Initialization.prepare_map
#audit axioms Rumoca.Initialization.prepare_initial
#audit axioms Rumoca.Initialization.prepare_no_binding
#audit axioms Rumoca.Initialization.prepare_fallback_notice
#audit axioms Rumoca.Initialization.prepare_selection_notice
#audit axioms Rumoca.Initialization.prepare_default
#audit axioms Rumoca.Initialization.constant_binding_inconsistent
#audit axioms Rumoca.Initialization.prepare_sound
#audit axioms Rumoca.Initialization.prepare_complete
#audit axioms Rumoca.Initialization.completed_solution_unique
#audit axioms Rumoca.Initialization.unfixed_start_is_free
#audit axioms Rumoca.Initialization.diagnostics_notice
#audit axioms Rumoca.Initialization.diagnostics_span
#audit axioms Rumoca.Initialization.forModel_state
#audit axioms Rumoca.Initialization.forModel_notices

#audit axioms Rumoca.Binary64.round_spec
#audit axioms Rumoca.Binary64.rounding_unique
#audit axioms Rumoca.Binary64.advance_no_overflow
#audit axioms Rumoca.Binary64.advance_exact
#audit axioms Rumoca.Binary64.advance_half_spacing
#audit axioms Rumoca.Binary64.run_error
#audit axioms Rumoca.Binary64.advance_half
#audit axioms Rumoca.Binary64.round_zero
#audit axioms Rumoca.Binary64.roundedAdd_negative_zero
#audit axioms Rumoca.Binary64.roundedAdd_positive_zero
#audit axioms Rumoca.Binary64.ofBits_toBits
#audit axioms Rumoca.Binary64.toBits_ofBits
#audit axioms Rumoca.Binary64.toBits_exponent
#audit axioms Rumoca.Binary64.signed_zero_bits
#audit axioms Rumoca.Binary64.run_exact
#audit axioms Rumoca.Transition.Machine.behavior_iff
#audit axioms Rumoca.Transition.FunctionalBisimulation.behaviors
#audit axioms Rumoca.Profile.behavior_congr
#audit axioms Rumoca.Profile.behavior_iff
#audit axioms Rumoca.ModelExchange.get_set
#audit axioms Rumoca.ModelExchange.derivative_correct
#audit axioms Rumoca.UnitSolver.step_correct
#audit axioms Rumoca.UnitSolver.step_no_overflow
#audit axioms Rumoca.CoSimulation.run_model_correct
#audit axioms Rumoca.CoSimulation.run_progress
#audit axioms Rumoca.Solve.Tensor.Program.eval_correct
#audit axioms Rumoca.Tensor.Value.toMatrix_ofMatrix
#audit axioms Rumoca.Tensor.Value.ofMatrix_toMatrix
#audit axioms Rumoca.Solve.driven_rhs
#audit axioms Rumoca.Solve.driven_initial
#audit axioms Rumoca.Solve.driven_outputs
#audit axioms Rumoca.Solve.driven_compact
#audit axioms Rumoca.Solve.ModelData.names_unique
#audit axioms Rumoca.Driven.Solved.Model.export_problem
#audit axioms Rumoca.Driven.Solved.Model.export_state_name
#audit axioms Rumoca.Driven.Solved.Model.export_input_name
#audit axioms Rumoca.Driven.Flat.lower_correct
#audit axioms Rumoca.Driven.DAE.lower_correct
#audit axioms Rumoca.Driven.Solved.lower_correct
#audit axioms Rumoca.Driven.lowering_chain_correct
#audit axioms Rumoca.Driven.Flat.lower_initial
#audit axioms Rumoca.Driven.DAE.lower_initial
#audit axioms Rumoca.Driven.Solved.lower_initial
#audit axioms Rumoca.Driven.initialization_chain_correct
#audit axioms Rumoca.Pass.preserves_compose
#audit axioms Rumoca.Pass.preserves_property
#audit axioms Rumoca.Solve.FMI3Model.time_distinct
#audit axioms Rumoca.Solve.FMI3Model.prepared_solve
#audit axioms Rumoca.Solve.FMI3Model.rhs_correct
#audit axioms Rumoca.FMI3.allowed_correct
#audit axioms Rumoca.Transition.Machine.step_behaviors
#audit axioms Rumoca.Transition.Machine.prefix_behaviors
#audit axioms Rumoca.FMI3.nominals_reject_instantiated
#audit axioms Rumoca.FMI3.invalid_call_error
#audit axioms Rumoca.FMI3.invalid_call_final_values
#audit axioms Rumoca.FMI3.terminated_me_queries
#audit axioms Rumoca.FMI3.reset_recovers
#audit axioms Rumoca.FMI3.me_initialization
#audit axioms Rumoca.FMI3.cs_initialization
#audit axioms Rumoca.FMI3.cs_cannot_use_me_set_time
#audit axioms Rumoca.Float64.decode_finite
#audit axioms Rumoca.Float64.decode_nan
#audit axioms Rumoca.Float64.value_eq_iff
#audit axioms Rumoca.Float64.value_lt_iff
#audit axioms Rumoca.Float64.value_le_iff
#audit axioms Rumoca.Float64.test_finite
#audit axioms Rumoca.Float64.test_finite_false
#audit axioms Rumoca.Float64.unordered_left
#audit axioms Rumoca.Float64.unordered_right
#audit axioms Rumoca.FMI3.Time.admissible_iff
#audit axioms Rumoca.FMI3.Time.initial_lower
#audit axioms Rumoca.FMI3.Time.maximum_value
#audit axioms Rumoca.FMI3.Time.initial_represents
#audit axioms Rumoca.FMI3.Time.setTime_represents
#audit axioms Rumoca.FMI3.Time.completed_represents
#audit axioms Rumoca.FMI3.Time.event_represents
#audit axioms Rumoca.FMI3.Time.step_represents
#audit axioms Rumoca.FMI3.Time.trace_represents
#audit axioms Rumoca.FMI3.Initialization.above_iff
#audit axioms Rumoca.FMI3.Initialization.stopTime_defined
#audit axioms Rumoca.FMI3.Initialization.stopTime_bits

#audit axioms Rumoca.GALEC.execute_correct

#audit axioms Rumoca.Solve.Algorithm.lowerExpr_correct

#audit axioms Rumoca.Solve.Algorithm.lower_correct

#audit axioms Rumoca.Solve.Algorithm.lower_trace_correct

#audit axioms Rumoca.GALEC.UnitProfile.lower_correct

#audit axioms Rumoca.GALEC.UnitProfile.startup_initializes

#audit axioms Rumoca.GALEC.UnitProfile.clock_preserved

#audit axioms Rumoca.GALEC.Protocol.read_only_idle

#audit axioms Rumoca.GALEC.Protocol.tick_enters_once

#audit axioms Rumoca.GALEC.Protocol.stopped_terminal

#audit axioms Rumoca.GALEC.Protocol.lower_trace_correct
