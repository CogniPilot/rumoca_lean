import Rumoca.FMI3PublicContracts
import Rumoca.FMI3CapabilityProofs
import Rumoca.FMI3AbsentVariableProofs
import Rumoca.FMI3DiscreteEvaluationProofs
import Rumoca.FMI3EventIndicatorProofs
import Rumoca.FMI3CSMixedRun
import Rumoca.FMI3DebugLoggingProofs
import Rumoca.FMI3InitializationProtocol
import Rumoca.FMI3CSProtocolRuntime
import Rumoca.FMI3MEProtocolRuntime
import Rumoca.FMI3CreatedInitializationProtocol
import Rumoca.FMI3InitializationProtocolME
import Rumoca.FMI3InitializationProtocolCS
import Rumoca.FMI3InitializationRestart
import Rumoca.FMI3SimulationRestart
import Rumoca.FMI3Float64Rejection
import Rumoca.FMI3InitializationMERun
import Rumoca.FMI3InitializationCSRun
import Rumoca.FMI3CreatedInitializationAccess
import Rumoca.FMI3InitializationAccess
import Rumoca.FMI3Float64Environment
import Rumoca.FMI3Float64SetEnvironment
import Rumoca.FMI3MEMixedLifecycle
import Rumoca.FMI3MEMixedRun
import Rumoca.FMI3MEFailureRecovery
import Rumoca.FMI3MENumericalRunLifecycle
import Rumoca.FMI3MENumericalLifecycle
import Rumoca.FMI3MENumericalHistory
import Rumoca.FMI3MENumericalEnvironment
import Rumoca.FMI3StateEnvironment
import Rumoca.FMI3CSLoggedLifecycle
import Rumoca.FMI3CSRunLogging
import Rumoca.FMI3CSRunLifecycle
import Rumoca.FMI3CSRun
import Rumoca.FMI3Recovery
import Rumoca.FMI3CSLifecycle
import Rumoca.FMI3CSRelease
import Rumoca.FMI3StepProofs
import Rumoca.FMI3RuntimeEnvironment
import Rumoca.FMI3ModelAdvance
import Rumoca.FMI3MELifecycle
import Rumoca.FMI3MEInitialization
import Rumoca.FMI3MERelease
import Rumoca.FMI3TimeProofs
import Rumoca.FMI3MEHistory
import Rumoca.FMI3TerminationRelease
import Rumoca.FMI3TerminationProofs
import Rumoca.FMI3StaticReset
import Rumoca.FMI3StaticInitializationErrors
import Rumoca.FMI3InitializationSemantics
import Rumoca.FMI3InitializationCalls
import Rumoca.FMI3InitializationProofs
import Rumoca.FMI3Float64SetProofs
import Rumoca.FMI3Float64Proofs
import Rumoca.FMI3DerivativeProofs
import Rumoca.FMI3StateProofs
import Rumoca.FMI3NominalProofs
import Rumoca.FMI3LoggingProofs
import Rumoca.FMI3LiteralProofs
import ProofAudit.Audit
import Rumoca.FMI3FactoryValidation
import Rumoca.FMI3FactoryAdmission
import Rumoca.FMI3StaticCreation
import Rumoca.FMI3StaticLogging
import Rumoca.FMI3StaticRejection
import Rumoca.FMI3StaticLifecycle
import Rumoca.FMI3StaticInitialization
import Rumoca.Behavioral
import Rumoca.Compiler
import Rumoca.Lowering
import Rumoca.Semantics
import Rumoca.Source
import Rumoca.Verified
import Rumoca.ArrayProofs
import Rumoca.FMI3CountProofs
import Rumoca.FMI3VersionProofs
import Rumoca.ParseFilesProofs
import Rumoca.Provenance
import Rumoca.Initialization
import Rumoca.InitializationDiagnosticProofs
import Rumoca.TensorProduction
import Rumoca.TensorAdapterChars
import Rumoca.ConstantProofs
import Rumoca.EFMITensorArchiveProofs

#audit axioms Rumoca.Artifact.source_identity
#audit axioms Rumoca.FMI3.adapter_me_calls
#audit axioms Rumoca.FMI3.MEHistory.source_frame
#audit axioms Rumoca.FMI3.adapter_me_history
#audit axioms Rumoca.Artifact.initializationDiagnostics_eq_forModel
#audit axioms Rumoca.Artifact.initializationDiagnostic_count
#audit axioms Rumoca.Artifact.initializationDiagnostic_state
#audit axioms Rumoca.Source.initializes_iff
#audit axioms Rumoca.Flat.Model.initialization_matches
#audit axioms Rumoca.DAE.Model.initialization_matches
#audit axioms Rumoca.Solve.Model.initialization_checked_real
#audit axioms Rumoca.Solve.Model.initialization_correct
#audit axioms Rumoca.Solve.Model.initialized_solution_unique
#audit axioms Rumoca.Solve.FMI3Model.initialization_matches
#audit axioms Rumoca.GALEC.initialization_matches

#audit axioms Rumoca.Artifact.source_locations
#audit axioms Rumoca.compile_resolve_error
#audit axioms Rumoca.compile_error_after_parse

#audit axioms Rumoca.CLI.analyze_eq_reference
#audit axioms Rumoca.CLI.analyze_json
#audit axioms Rumoca.CLI.analyze_failure
#audit axioms Rumoca.CLI.analyze_terminal
#audit axioms Rumoca.CLI.analyze_batch

#audit axioms Rumoca.FMI3.counts_source
#audit axioms Rumoca.FMI3.counts_failure_source
#audit axioms Rumoca.FMI3.counts_runtime_source
#audit axioms Rumoca.FMI3.version_source
#audit axioms Rumoca.FMI3.literal_events_source
#audit axioms Rumoca.FMI3.sourceBuild_correct
#audit axioms Rumoca.FMI3.reset_result
#audit axioms Rumoca.FMI3.reset_source
#audit axioms Rumoca.FMI3.compile_reset_verified
#audit axioms Rumoca.FMI3.compile_rendered_reset_verified
#audit axioms Rumoca.FMI3.adapter_chars
#audit axioms Rumoca.FMI3.adapter_correct
#audit axioms Rumoca.FMI3.adapter_identity
#audit axioms Rumoca.FMI3.parsed_state_name
#audit axioms Rumoca.FMI3.compiled_token_ascii
#audit axioms Rumoca.FMI3.compiled_token_content
#audit axioms Rumoca.FMI3.Identity.prepared_factory_validation
#audit axioms Rumoca.FMI3.adapter_preprocessed
#audit axioms Rumoca.FMI3.adapter_reset_syntax
#audit axioms Rumoca.FMI3.adapter_reset_tokenization
#audit axioms Rumoca.FMI3.adapter_functions_tokenization
#audit axioms Rumoca.FMI3.adapter_call_entry
#audit axioms Rumoca.FMI3.adapter_reset_source
#audit axioms Rumoca.FMI3.lexed_name
#audit axioms Rumoca.FMI3.parsed_name
#audit axioms Rumoca.FMI3.parsed_modelIdentifier
#audit axioms Rumoca.FMI3.parsed_functionPrefix

#audit axioms Rumoca.ArrayCompiler.Prepared.source_correct
#audit axioms Rumoca.ArrayCompiler.Prepared.equation_correct
#audit axioms Rumoca.ArrayCompiler.Prepared.initialization_correct
#audit axioms Rumoca.ArrayCompiler.prepare_correct

#audit axioms Rumoca.compile_complete
#audit axioms Rumoca.compile_eq_parsed
#audit axioms Rumoca.flatten_correct
#audit axioms Rumoca.dae_correct
#audit axioms Rumoca.solve_correct
#audit axioms Rumoca.compiler_correct
#audit axioms Rumoca.ideal_samples_refine_solution
#audit axioms Rumoca.ideal_end_to_end
#audit axioms Rumoca.emitted_text_is_unit
#audit axioms Rumoca.execution_correct
#audit axioms Rumoca.artifact_correct
#audit axioms Rumoca.compile_verified
#audit axioms Rumoca.Flat.lower_correct
#audit axioms Rumoca.DAE.lower_correct
#audit axioms Rumoca.Solve.lower_correct
#audit axioms Rumoca.lowering_chain_correct
#audit axioms Rumoca.Source.solution_unique
#audit axioms Rumoca.Source.rounded_samples_unique
#audit axioms Rumoca.Solve.lower_samples_correct
#audit axioms Rumoca.CStatements.lower_behavior_correct
#audit axioms Rumoca.CStatements.real_refinement
#audit axioms Rumoca.compiler_semantic_preservation
#audit axioms Rumoca.Flat.behavior_correct
#audit axioms Rumoca.DAE.behavior_correct
#audit axioms Rumoca.Solve.behavior_correct
#audit axioms Rumoca.CStatements.solve_behavior_correct
#audit axioms Rumoca.lowering_chain_behavior_correct
#audit axioms Rumoca.compiler_preserves_property
#audit axioms Rumoca.CStatements.model_exchange_correct
#audit axioms Rumoca.CStatements.co_simulation_correct

#audit axioms Rumoca.FMI3.logging_source

#audit axioms Rumoca.FMI3.nominals_source

#audit axioms Rumoca.FMI3.state_access_source

#audit axioms Rumoca.FMI3.derivative_value_source
#audit axioms Rumoca.FMI3.derivative_call_source
#audit axioms Rumoca.FMI3.derivative_source

#audit axioms Rumoca.FMI3.float64_source

#audit axioms Rumoca.FMI3.float64_set_source

#audit axioms Rumoca.FMI3.InitializationCalls.model_source_initialized
#audit axioms Rumoca.FMI3.InitializationCalls.source_initialized_unique
#audit axioms Rumoca.FMI3.InitializationCalls.exited_source_initialized
#audit axioms Rumoca.FMI3.InitializationCalls.QuietExecutionContract.source
#audit axioms Rumoca.FMI3.InitializationCalls.QuietExecutionContract.source_contract
#audit axioms Rumoca.FMI3.initialization_source

#audit axioms Rumoca.FMI3.adapter_factory_admission
#audit axioms Rumoca.FMI3.adapter_static_runtime
#audit axioms Rumoca.FMI3.adapter_static_definitions
#audit axioms Rumoca.FMI3.prepared_static_identity
#audit axioms Rumoca.FMI3.adapter_quiet_static_creation
#audit axioms Rumoca.FMI3.adapter_logged_static_creation
#audit axioms Rumoca.FMI3.prepared_static_rejection
#audit axioms Rumoca.FMI3.adapter_quiet_static_rejection
#audit axioms Rumoca.FMI3.adapter_logged_static_rejection
#audit axioms Rumoca.FMI3.StaticFactory.Created.source_default
#audit axioms Rumoca.FMI3.adapter_static_create_release
#audit axioms Rumoca.FMI3.adapter_static_null_release
#audit axioms Rumoca.FMI3.adapter_static_initialization
#audit axioms Rumoca.FMI3.adapter_static_create_initialize
#audit axioms Rumoca.FMI3.FactoryValidation.prepared_public_admission
#audit axioms Rumoca.FMI3.FactoryValidation.actual_adapter_admission

#audit axioms Rumoca.FMI3.adapter_static_initialization_complete

#audit axioms Rumoca.FMI3.adapter_static_reset
#audit axioms Rumoca.FMI3.adapter_static_reset_initialize

#audit axioms Rumoca.FMI3.adapter_termination
#audit axioms Rumoca.FMI3.Termination.source_frame
#audit axioms Rumoca.FMI3.adapter_initialize_terminate

#audit axioms Rumoca.FMI3.adapter_termination_release

#audit axioms Rumoca.FMI3.adapter_time
#audit axioms Rumoca.FMI3.TimeCalls.source_frame
#audit axioms Rumoca.FMI3.adapter_time_history

#audit axioms Rumoca.FMI3.adapter_initialize_me_history
#audit axioms Rumoca.FMI3.adapter_me_release
#audit axioms Rumoca.FMI3.adapter_initialize_me_release

#audit axioms Rumoca.FMI3.adapter_create_me_release

#audit axioms Rumoca.FMI3.ModelAdvance.source_error
#audit axioms Rumoca.FMI3.adapter_model_advance

#audit axioms Rumoca.FMI3.adapter_runtime_environment
#audit axioms Rumoca.FMI3.adapter_runtime_time_history

#audit axioms Rumoca.FMI3.adapter_cs_calls

#audit axioms Rumoca.FMI3.CSHistory.source_error
#audit axioms Rumoca.FMI3.adapter_cs_history
#audit axioms Rumoca.FMI3.adapter_initialize_cs_history
#audit axioms Rumoca.FMI3.adapter_initialize_cs_release

#audit axioms Rumoca.FMI3.adapter_create_cs_release

#audit axioms Rumoca.FMI3.restart_correct
#audit axioms Rumoca.FMI3.adapter_suppressed_recovery
#audit axioms Rumoca.FMI3.adapter_logged_recovery

#audit axioms Rumoca.FMI3.CSRun.SourceEpoch.unique
#audit axioms Rumoca.FMI3.CSRun.source_epoch
#audit axioms Rumoca.FMI3.CSRun.Stored.source_observation
#audit axioms Rumoca.FMI3.CSRun.Stored.source_sample
#audit axioms Rumoca.FMI3.CSRun.Stored.restart_source_checkpoint
#audit axioms Rumoca.FMI3.CSRun.SemanticAction.source_observations
#audit axioms Rumoca.FMI3.CSRun.SemanticTrace.source_observations
#audit axioms Rumoca.FMI3.adapter_cs_run_history

#audit axioms Rumoca.FMI3.adapter_create_cs_run_release

#audit axioms Rumoca.FMI3.CSRun.LoggedTrace.source_observation
#audit axioms Rumoca.FMI3.adapter_logged_cs_run_history

#audit axioms Rumoca.FMI3.adapter_create_logged_cs_release

#audit axioms Rumoca.FMI3.adapter_state_environment

#audit axioms Rumoca.FMI3.adapter_me_numerical_environment
#audit axioms Rumoca.FMI3.runtime_derivative_source

#audit axioms Rumoca.FMI3.adapter_me_environment
#audit axioms Rumoca.FMI3.MENumericalHistory.observations_source
#audit axioms Rumoca.FMI3.runtime_me_numerical_history

#audit axioms Rumoca.FMI3.runtime_create_me_numerical_release

#audit axioms Rumoca.FMI3.MENumericalRun.observations_source
#audit axioms Rumoca.FMI3.MENumericalRun.Calls.epochs_source
#audit axioms Rumoca.FMI3.runtime_create_me_run_release

#audit axioms Rumoca.FMI3.MEFailure.Recovery.source
#audit axioms Rumoca.FMI3.MEFailure.runtime_recovery
#audit axioms Rumoca.FMI3.MEFailure.Recovery.executed_source

#audit axioms Rumoca.FMI3.MEMixedRun.ActionContract.epochs_source
#audit axioms Rumoca.FMI3.MEMixedRun.Trace.source
#audit axioms Rumoca.FMI3.MEMixedRun.runtime_history

#audit axioms Rumoca.FMI3.MEMixedRun.runtime_create_release

#audit axioms Rumoca.FMI3.float64_set_runtime_source

#audit axioms Rumoca.FMI3.float64_runtime_source

#audit axioms Rumoca.FMI3.InitializationAccess.Certificate.completed_source
#audit axioms Rumoca.FMI3.InitializationAccess.source_contract
#audit axioms Rumoca.FMI3.InitializationAccess.runtime_source

#audit axioms Rumoca.FMI3.InitializationAccess.runtime_create_release

#audit axioms Rumoca.FMI3.InitializationAccess.RunOutcome.restored
#audit axioms Rumoca.FMI3.InitializationAccess.Certificate.cs_continuation
#audit axioms Rumoca.FMI3.InitializationAccess.runtime_create_cs_histories

#audit axioms Rumoca.FMI3.InitializationAccess.Certificate.me_continuation
#audit axioms Rumoca.FMI3.InitializationAccess.runtime_create_me_histories

#audit axioms Rumoca.FMI3.InitializationAccess.Recovery.completed_source
#audit axioms Rumoca.FMI3.Float64Rejection.Returned.source_recovery
#audit axioms Rumoca.FMI3.Float64Rejection.runtime_source

#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.source_ivp
#audit axioms Rumoca.FMI3.InitializationProtocol.Checkpoints.source_ivps
#audit axioms Rumoca.FMI3.InitializationProtocol.source_contract
#audit axioms Rumoca.FMI3.InitializationProtocol.runtime_source

#audit axioms Rumoca.FMI3.InitializationProtocol.after_creation
#audit axioms Rumoca.FMI3.InitializationProtocol.runtime_create_release
#audit axioms Rumoca.FMI3.InitializationProtocol.CreatedSourceContract.me_continuation
#audit axioms Rumoca.FMI3.InitializationProtocol.CreatedSourceContract.cs_continuation

#audit axioms Rumoca.FMI3.InitializationProtocol.RestartSourceContract.progress
#audit axioms Rumoca.FMI3.InitializationProtocol.RestartSourceContract.completed
#audit axioms Rumoca.FMI3.InitializationProtocol.restart_source
#audit axioms Rumoca.FMI3.InitializationProtocol.runtime_restart_source
#audit axioms Rumoca.FMI3.InitializationProtocol.restart_after_me
#audit axioms Rumoca.FMI3.InitializationProtocol.restart_after_cs
#audit axioms Rumoca.FMI3.CSProtocol.Ready.initialization
#audit axioms Rumoca.FMI3.CSProtocol.Ready.simulation
#audit axioms Rumoca.FMI3.CSProtocol.CycleContract.completed
#audit axioms Rumoca.FMI3.CSProtocol.cycle_contract
#audit axioms Rumoca.FMI3.CSProtocol.CycleContract.progress
#audit axioms Rumoca.FMI3.CSProtocol.CycleContract.restarted
#audit axioms Rumoca.FMI3.CSProtocol.correct
#audit axioms Rumoca.FMI3.CSProtocol.InitializationCompiler.interrupted
#audit axioms Rumoca.FMI3.CSProtocol.SimulationCompiler.interrupted
#audit axioms Rumoca.FMI3.CSProtocol.interrupted_correct
#audit axioms Rumoca.FMI3.CSProtocol.Contract.stopped_source
#audit axioms Rumoca.FMI3.CSProtocol.Contract.progress_source
#audit axioms Rumoca.FMI3.CSProtocol.Contract.released
#audit axioms Rumoca.FMI3.CSProtocol.runtime_create_release

#audit axioms Rumoca.FMI3.MEMixedRun.Trace.interrupted_source
#audit axioms Rumoca.FMI3.MEMixedRun.Trace.stopped_source

#audit axioms Rumoca.FMI3.InitializationProtocol.SourcePrefix.of_compiler
#audit axioms Rumoca.FMI3.MEProtocol.InitializationCompiler.interrupted
#audit axioms Rumoca.FMI3.MEProtocol.SimulationCompiler.interrupted
#audit axioms Rumoca.FMI3.MEProtocol.Ready.initialization
#audit axioms Rumoca.FMI3.MEProtocol.Ready.simulation
#audit axioms Rumoca.FMI3.MEProtocol.CycleContract.completed
#audit axioms Rumoca.FMI3.MEProtocol.cycle_contract
#audit axioms Rumoca.FMI3.MEProtocol.CycleContract.progress
#audit axioms Rumoca.FMI3.MEProtocol.CycleContract.restarted
#audit axioms Rumoca.FMI3.MEProtocol.interrupted_correct
#audit axioms Rumoca.FMI3.MEProtocol.correct
#audit axioms Rumoca.FMI3.MEProtocol.Contract.stopped_source
#audit axioms Rumoca.FMI3.MEProtocol.Contract.progress_source
#audit axioms Rumoca.FMI3.MEProtocol.Contract.released
#audit axioms Rumoca.FMI3.MEProtocol.runtime_create_release

#audit axioms Rumoca.FMI3.nominals_runtime_source

#audit axioms Rumoca.FMI3.debug_logging_source

#audit axioms Rumoca.FMI3.CSMixedRun.Execution.recorded_source

#audit axioms Rumoca.FMI3.CSMixedRun.Trace.completed_source

#audit axioms Rumoca.FMI3.CSMixedRun.Trace.recorded_source

#audit axioms Rumoca.FMI3.CSMixedRun.Trace.stopped_source

#audit axioms Rumoca.FMI3.CSMixedRun.runtime_history

#audit axioms Rumoca.FMI3.event_indicators_me_source
#audit axioms Rumoca.FMI3.event_indicators_source

#audit axioms Rumoca.FMI3.discrete_evaluation_source

#audit axioms Rumoca.FMI3.absent_variables_source

-- Existing unsupported public calls, their printers and actual-source contracts.
#audit axioms Rumoca.FMI3.capabilities_source
#audit axioms Rumoca.FMI3.scheduled_creation_source
#audit axioms Rumoca.FMI3.adapter_public_contracts
#audit axioms Rumoca.FMI3.public_functions_source

-- Development tensor artifact compiler path and its composed source-build contract.
#audit axioms Rumoca.tensorSourceBuild_correct
#audit axioms Rumoca.compileTensor_eq
#audit axioms Rumoca.ArrayCompiler.prepare_eq_parsed
#audit axioms Rumoca.compileTensor_eq_parsed
#audit axioms Rumoca.compileTensor_complete
#audit axioms Rumoca.TensorArtifact.ast_determined
#audit axioms Rumoca.TensorArtifact.tensorModel_square
#audit axioms Rumoca.TensorArtifact.name_square
#audit axioms Rumoca.TensorKernel.chars
#audit axioms Rumoca.FMI3.TensorFunctions.tensor_adapter_chars

-- Development tensor eFMU archive assembly and its composed contracts.
#audit axioms Rumoca.tensor_algorithm_correct
#audit axioms Rumoca.tensor_production_correct
#audit axioms Rumoca.tensor_manifests_correct_of_documents
#audit axioms Rumoca.tensor_archive_correct
#audit axioms Rumoca.TensorArchiveContract.code_members
#audit axioms Rumoca.TensorArchiveContract.schema_members
#audit axioms Rumoca.TensorArchiveContract.roster

-- G01 constant-rate development profile: preparation and its instantaneous contract.
#audit axioms Rumoca.ConstantCompiler.Prepared.source_correct
#audit axioms Rumoca.ConstantCompiler.Prepared.equation_correct
#audit axioms Rumoca.ConstantCompiler.Prepared.initialization_correct
#audit axioms Rumoca.ConstantCompiler.Prepared.rate_exact
#audit axioms Rumoca.ConstantCompiler.prepare_correct
#audit axioms Rumoca.ConstantCompiler.prepare_eq_parsed
#audit axioms Rumoca.ConstantCompiler.prepare_perm_invariant
