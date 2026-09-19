import RumocaFMI3.PublicAPI
import RumocaFMI3.CapabilityRejectionFamily
import RumocaFMI3.CapabilityMetadata
import RumocaFMI3.InitializationProtocolAbsent
import RumocaFMI3.AbsentVariableRequests
import RumocaFMI3.AbsentVariableContract
import RumocaFMI3.AbsentVariableSelection
import RumocaFMI3.InitializationProtocolEvaluation
import RumocaFMI3.DiscreteEvaluationMetadata
import RumocaFMI3.DiscreteEvaluationContract
import RumocaFMI3.InitializationProtocolEventIndicators
import RumocaFMI3.MEEventIndicatorExecution
import RumocaFMI3.CSMixedExecution
import RumocaFMI3.CSMixedPrefixes
import RumocaFMI3.CSMixedLifecycle
import RumocaFMI3.CSMixedInterrupted
import RumocaFMI3.CSMixedHandoff
import RumocaFMI3.CSRunInterrupted
import RumocaFMI3.LoggingCapabilityEffects
import RumocaFMI3.CSLoggingMemory
import RumocaFMI3.MELoggingMemory
import RumocaFMI3.CSLoggingCalls
import RumocaFMI3.MELoggingCalls
import RumocaFMI3.DebugLoggingInitialization
import RumocaFMI3.DebugLoggingInputFrame
import RumocaFMI3.InitializationProtocolInputs
import RumocaFMI3.InitializationProtocolLogging
import RumocaFMI3.InitializationRetention
import RumocaFMI3.LoggingCapability
import RumocaFMI3.LoggingCapabilityCS
import RumocaFMI3.LoggingCapabilityCalls
import RumocaFMI3.LoggingCapabilityCreation
import RumocaFMI3.LoggingCapabilityEnvironment
import RumocaFMI3.LoggingCapabilityFrames
import RumocaFMI3.LoggingCapabilityLifetime
import RumocaFMI3.LoggingCapabilityViews
import RumocaFMI3.LoggingRequests
import RumocaFMI3.DebugLoggingContract
import RumocaFMI3.InitializationProtocol
import RumocaFMI3.InitializationProtocolEnvironment
import RumocaFMI3.InitializationSimulation
import RumocaFMI3.InitializationMESimulation
import RumocaFMI3.MEMixedInterrupted
import RumocaFMI3.CSInitializationProtocol
import RumocaFMI3.CSProtocolInterrupted
import RumocaFMI3.MEProtocolInterrupted
import RumocaFMI3.InitializationProtocolCreation
import RumocaFMI3.InitializationProtocolHandoff
import RumocaFMI3.InitializationProtocolRunFrames
import RumocaFMI3.InitializationProtocolRestart
import RumocaFMI3.MESimulationStorage
import RumocaFMI3.CSSimulationStorage
import RumocaFMI3.RestartStorage
import RumocaFMI3.InitializationProtocolCalls
import RumocaFMI3.InitializationProtocolHistory
import RumocaFMI3.InitializationProtocolLifetime
import RumocaFMI3.InitializationProtocolRejection
import RumocaFMI3.InitializationProtocolStorage
import RumocaFMI3.Float64RawBuffers
import RumocaFMI3.Float64Rejection
import RumocaFMI3.Float64RejectionPreparation
import RumocaFMI3.LifecycleStorage
import RumocaFMI3.Float64RejectionMemory
import RumocaFMI3.InitializationAccessReset
import RumocaFMI3.Float64RejectionExecution
import RumocaFMI3.LifecycleEnvironment
import RumocaFMI3.ResetStorage
import RumocaFMI3.InitializationMERun
import RumocaFMI3.CSRunEnvironment
import RumocaFMI3.InitializationCSRun
import RumocaFMI3.CSRunCompleted
import RumocaFMI3.CSRunProgress
import RumocaFMI3.InitializationAccessStorage
import RumocaFMI3.InitializationAccess
import RumocaFMI3.InitializationRuntime
import RumocaFMI3.Float64Environment
import RumocaFMI3.Float64SetEnvironment
import RumocaFMI3.MEMixedLifecycle
import RumocaFMI3.MEMixedExecution
import RumocaFMI3.MEFailureRecovery
import RumocaFMI3.MEFailureContracts
import RumocaFMI3.MENumericalRunLifecycle
import RumocaFMI3.MENumericalLifecycle
import RumocaFMI3.MENumericalHistory
import RumocaFMI3.MEControlEnvironment
import RumocaFMI3.DerivativeEnvironment
import RumocaFMI3.StateEnvironment
import RumocaFMI3.CSRunStatus
import RumocaFMI3.CSRunLoggedExecution
import RumocaFMI3.CSRunFinish
import RumocaFMI3.CSRunFrames
import RumocaFMI3.CSRunExecution
import RumocaFMI3.StepRecovery
import RumocaFMI3.FactoryEnvironment
import RumocaFMI3.CSCreationStorage
import RumocaFMI3.CSLifecycle
import RumocaFMI3.CSInitialization
import RumocaFMI3.InitializationEnvironment
import RumocaFMI3.CSRelease
import RumocaFMI3.TerminationEnvironment
import RumocaFMI3.StepContract
import RumocaFMI3.StepCases
import RumocaFMI3.StepDiscard
import RumocaFMI3.StepFailures
import RumocaFMI3.StepArguments
import RumocaFMI3.ErrorContext
import RumocaFMI3.StepErrors
import RumocaFMI3.StepEntry
import RumocaFMI3.StepGuards
import RumocaFMI3.RuntimeEnvironment
import RumocaFMI3.StepAdmission
import RumocaFMI3.StepAdvance
import RumocaFMI3.ModelAdvance
import RumocaFMI3.StaticFactoryAcquisition
import RumocaFMI3.MELifecycle
import RumocaFMI3.MEInitialization
import RumocaFMI3.MEAtomicFrames
import RumocaFMI3.MERelease
import RumocaFMI3.MEHistory
import RumocaFMI3.EventEntryCalls
import RumocaFMI3.EventEntryContract
import RumocaFMI3.EventEntryHistory
import RumocaFMI3.CompletedCalls
import RumocaFMI3.CompletedContract
import RumocaFMI3.CompletedHistory
import RumocaFMI3.DiscreteCalls
import RumocaFMI3.DiscreteContract
import RumocaFMI3.DiscreteHistory
import RumocaFMI3.TimeContract
import RumocaFMI3.TimeHistory
import RumocaFMI3.TerminationRelease
import RumocaFMI3.TerminationContract
import RumocaFMI3.StaticReset
import RumocaFMI3.StaticErrorCalls
import RumocaFMI3.StaticInitializationErrors
import RumocaFMI3.StaticSlots
import RumocaFMI3.StaticInitialization
import RumocaFMI3.AtomicSlots
import RumocaFMI3.SlotExecution
import RumocaFMI3.IdentityContract
import RumocaFMI3.IdentityFactoryEntry
import RumocaFMI3.IdentityNames
import RumocaFMI3.FactoryNull
import RumocaFMI3.FactoryAdmissionContract
import RumocaFMI3.InstanceStorage
import RumocaFMI3.StaticFactoryReservation
import RumocaFMI3.StaticFactoryEnvironment
import RumocaFMI3.StaticFactoryExhaustion
import RumocaFMI3.StaticFactoryCreation
import RumocaFMI3.StaticRelease
import RumocaFMI3.StaticFactoryOwnership
import RumocaFMI3.StaticFactoryAdmission
import RumocaFMI3.StaticFactoryRejection
import RumocaFMI3.StaticFactoryPrinter
import RumocaFMI3.StaticStorageCalls
import RumocaFMI3.StaticRuntimeContract
import RumocaFMI3.StaticFactoryLiterals
import RumocaFMI3.InitializationArguments
import RumocaFMI3.InitializationContract
import RumocaFMI3.InitializationCalls
import RumocaFMI3.InitializationFailures
import RumocaFMI3.InitializationErrors
import RumocaFMI3.InitializationExit
import RumocaFMI3.InitializationComposition
import RumocaFMI3.InitializationExitErrors
import RumocaFMI3.InitializationQuiet
import RumocaFMI3.Float64SetEntry
import RumocaFMI3.Float64SetValidation
import RumocaFMI3.Float64SetWrite
import RumocaFMI3.Float64SetFailures
import RumocaFMI3.Float64SetMetadata
import RumocaFMI3.Float64SetContract
import RumocaFMI3.ArrayAccess
import RumocaFMI3.FailureSites
import RumocaFMI3.Float64Calls
import RumocaFMI3.Float64Validation
import RumocaFMI3.Float64Read
import RumocaFMI3.Float64Get
import RumocaFMI3.Float64Failures
import RumocaFMI3.Float64Metadata
import RumocaFMI3.Float64Contract
import RumocaFMI3.NumericalBindings
import RumocaFMI3.ModelRhs
import RumocaFMI3.TensorModelRhs
import RumocaFMI3.DerivativeCalls
import RumocaFMI3.DerivativeFailures
import RumocaFMI3.DerivativeContract
import RumocaFMI3.DerivativeMetadata
import RumocaFMI3.StateContract
import RumocaFMI3.StateMetadata
import RumocaFMI3.NominalContract
import RumocaFMI3.NominalMetadata
import RumocaFMI3.LiteralEvents
import RumocaFMI3.LoggingContract
import ProofAudit.Audit
import RumocaC.Codegen
import RumocaC.Execution
import RumocaC.Lowering
import RumocaC.Statements
import RumocaC.Syntax
import RumocaFMI3.CallProofs
import RumocaFMI3.BuildDescriptionProofs
import RumocaFMI3.SourceLinkageProofs
import RumocaC.Calls
import RumocaFMI3.DerivativeProofs
import RumocaC.Body
import RumocaFMI3.GuardProofs
import RumocaFMI3.HistoryBodies
import RumocaFMI3.InitializationBodies
import RumocaFMI3.InitializationEntry
import RumocaFMI3.ErrorCalls
import RumocaFMI3.LiteralPreparation
import RumocaFMI3.HeaderProofs
import RumocaFMI3.LiteralRejection

import RumocaFMI3.LifecycleGuard
import RumocaFMI3.LifecycleBodies
import RumocaFMI3.BodyEmbedding
import RumocaFMI3.RuntimePreprocessing
import RumocaFMI3.AdapterPreprocessing
import RumocaFMI3.AdapterPrinter
import RumocaFMI3.ErrorBodies
import RumocaFMI3.SetterScope
import RumocaFMI3.HistoryProofs
import RumocaC.Memory
import RumocaFMI3.Metadata
import RumocaFMI3.StateProofs
import RumocaFMI3.StateCalls
import RumocaFMI3.TimeProofs
import RumocaFMI3.ResetContract
import RumocaFMI3.CallTypes

import RumocaFMI3.CountQueries
import RumocaFMI3.CountContract
import RumocaFMI3.CountPool
import RumocaFMI3.CountMetadata
import RumocaFMI3.Version
import RumocaFMI3.VersionMetadata
import RumocaFMI3.TensorMetadata
import RumocaFMI3.TensorInstanceStorage
import RumocaFMI3.TensorInstanceRhs
import RumocaFMI3.TensorInstanceJacobian
import RumocaFMI3.TensorFloat64Access
import RumocaFMI3.TensorContinuousStates
import RumocaFMI3.TensorCountQueries
import RumocaFMI3.TensorSetTime
import RumocaFMI3.TensorReset
import RumocaFMI3.TensorLifecycleModes
import RumocaFMI3.TensorFree
import RumocaFMI3.TensorLifecycleHistory
import RumocaFMI3.TensorInstanceInit
import RumocaFMI3.TensorStaticFactory
import RumocaFMI3.TensorNominals
import RumocaFMI3.TensorVersion
import RumocaFMI3.TensorDebugLogging
import RumocaFMI3.TensorScheduledCreation
import RumocaFMI3.TensorDiscreteEvaluation
import RumocaFMI3.TensorDiscreteUpdate
import RumocaFMI3.TensorCompletedStep
import RumocaFMI3.TensorEventIndicators
import RumocaFMI3.TensorDoStep
import RumocaFMI3.TensorFunctions
import RumocaFMI3.TensorFamilyContracts
import RumocaFMI3.TensorStorageCode
import RumocaFMI3.ConstantInstanceInit
import RumocaFMI3.ConstantInstanceRhs
import RumocaFMI3.ConstantFloat64Access
import RumocaFMI3.ConstantDerivative
import RumocaFMI3.ConstantDoStep
import RumocaFMI3.TensorAdapterPrinter
import RumocaFMI3.TensorAdapterContract
import RumocaFMI3.ConstantFunctions
import RumocaFMI3.ConstantFamilyContracts
import RumocaFMI3.ConstantCallPolicy
import RumocaFMI3.ConstantAdapterPrinter
import RumocaFMI3.ConstantAdapterContract

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
#audit axioms Rumoca.FMI3.CountQueries.rendered_contract
#audit axioms Rumoca.FMI3.CountQueries.message_collected
#audit axioms Rumoca.FMI3.CountQueries.failure_reaches
#audit axioms Rumoca.FMI3.CountQueries.prepared_failure
#audit axioms Rumoca.FMI3.CountQueries.failure_prefix
#audit axioms Rumoca.FMI3.CountEnvironment.body_agrees
#audit axioms Rumoca.FMI3.CountEnvironment.quiet_correct
#audit axioms Rumoca.FMI3.CountEnvironment.QuietContract.returned
#audit axioms Rumoca.FMI3.CountEnvironment.suppressed_correct
#audit axioms Rumoca.FMI3.CountEnvironment.logged_correct
#audit axioms Rumoca.FMI3.CountEnvironment.prepared_correct
#audit axioms Rumoca.FMI3.CountQueries.written_store
#audit axioms Rumoca.FMI3.CountQueries.written_memory
#audit axioms Rumoca.FMI3.CountQueries.failed_memory
#audit axioms Rumoca.FMI3.CountAccess.Request.OutputStorage.preserved
#audit axioms Rumoca.FMI3.CountAccess.request_coverage
#audit axioms Rumoca.FMI3.CountMetadata.described_counts
#audit axioms Rumoca.FMI3.CountMetadata.artifact_counts
#audit axioms Rumoca.FMI3.ErrorCalls.failure_after_prefix
#audit axioms Rumoca.FMI3.LiteralPreparation.message_bound

#audit axioms Rumoca.FMI3.CallTypes.helpers_ready
#audit axioms Rumoca.FMI3.CallTypes.functions_ready
#audit axioms Rumoca.FMI3.CallTypes.value_reference_conversion
#audit axioms Rumoca.FMI3.CallTypes.value_reference_bits
#audit axioms Rumoca.FMI3.CallTypes.entry
#audit axioms Rumoca.FMI3.CallTypes.arguments_exist
#audit axioms Rumoca.FMI3.LiteralPreparation.definition_bound

#audit axioms Rumoca.FMI3.Header.commentText_reference
#audit axioms Rumoca.FMI3.Reset.tail_run
#audit axioms Rumoca.FMI3.Reset.body_run
#audit axioms Rumoca.FMI3.Reset.frame
#audit axioms Rumoca.FMI3.Reset.state
#audit axioms Rumoca.FMI3.Reset.history
#audit axioms Rumoca.FMI3.Reset.lifecycle
#audit axioms Rumoca.FMI3.Reset.stop
#audit axioms Rumoca.FMI3.Reset.other_instance
#audit axioms Rumoca.FMI3.Reset.retained_field
#audit axioms Rumoca.FMI3.Reset.parameters_bound
#audit axioms Rumoca.FMI3.Reset.call_reaches
#audit axioms Rumoca.FMI3.Reset.call_behaviors
#audit axioms Rumoca.FMI3.Reset.null_reaches
#audit axioms Rumoca.FMI3.Reset.null_behaviors
#audit axioms Rumoca.FMI3.Reset.correct
#audit axioms Rumoca.FMI3.Reset.Syntax.printed
#audit axioms Rumoca.FMI3.Reset.Syntax.render_denotes
#audit axioms Rumoca.FMI3.Reset.rendered_contract
#audit axioms Rumoca.FMI3.Reset.Printer.function_printable
#audit axioms Rumoca.FMI3.Reset.Printer.function_renders
#audit axioms Rumoca.FMI3.Reset.Printer.render_denotes
#audit axioms Rumoca.FMI3.RuntimePrinter.body_printable
#audit axioms Rumoca.FMI3.RuntimePrinter.function_printable
#audit axioms Rumoca.FMI3.RuntimePrinter.function_tokenization
#audit axioms Rumoca.FMI3.RuntimePrinter.helpers_printable
#audit axioms Rumoca.FMI3.AdapterPrinter.functions_printable
#audit axioms Rumoca.FMI3.AdapterPrinter.rendered_contract
#audit axioms Rumoca.FMI3.LiteralPreparation.rendered_member

#audit axioms Rumoca.FMI3.LiteralPreparation.rendered_functions
#audit axioms Rumoca.FMI3.Header.signatures_unique
#audit axioms Rumoca.FMI3.LiteralPreparation.function_bound
#audit axioms Rumoca.FMI3.LiteralRejection.rejection_message_collected
#audit axioms Rumoca.FMI3.LiteralRejection.rejection_message_bound
#audit axioms Rumoca.FMI3.LiteralRejection.nominal_reject
#audit axioms Rumoca.FMI3.LiteralPreparation.constants_covered
#audit axioms Rumoca.FMI3.LiteralPreparation.header_fresh
#audit axioms Rumoca.FMI3.LiteralPreparation.program_covered
#audit axioms Rumoca.FMI3.LiteralPreparation.helpers_bound
#audit axioms Rumoca.FMI3.LiteralPreparation.pool_complete
#audit axioms Rumoca.FMI3.LiteralPreparation.declarations_correct
#audit axioms Rumoca.FMI3.LiteralPreparation.body_calls
#audit axioms Rumoca.FMI3.LiteralPreparation.functions_calls
#audit axioms Rumoca.FMI3.LiteralPreparation.lowering_behaviors

#audit axioms Rumoca.FMI3.ErrorCalls.failure_parameters
#audit axioms Rumoca.FMI3.ErrorCalls.failure_reaches
#audit axioms Rumoca.FMI3.ErrorCalls.failure_statement_reaches
#audit axioms Rumoca.FMI3.ErrorCalls.nominal_parameters
#audit axioms Rumoca.FMI3.ErrorCalls.nominal_reject_reaches
#audit axioms Rumoca.FMI3.ErrorCalls.nominal_reject_correct

#audit axioms Rumoca.FMI3.metadata_name
#audit axioms Rumoca.FMI3.StateCalls.parameters_bound
#audit axioms Rumoca.FMI3.StateCalls.call_reaches
#audit axioms Rumoca.FMI3.StateCalls.get_reaches
#audit axioms Rumoca.FMI3.StateCalls.get_behaviors
#audit axioms Rumoca.FMI3.StateCalls.set_reaches
#audit axioms Rumoca.FMI3.StateCalls.set_behaviors
#audit axioms Rumoca.FMI3.Build.recipe_required
#audit axioms Rumoca.FMI3.Build.decode_recipe
#audit axioms Rumoca.FMI3.Build.invocation_required
#audit axioms Rumoca.FMI3.Build.description_valid
#audit axioms Rumoca.FMI3.Build.artifact_correct
#audit axioms Rumoca.FMI3.Build.configuration_valid
#audit axioms Rumoca.FMI3.NameParts.text
#audit axioms Rumoca.FMI3.modelIdentifier_parts
#audit axioms Rumoca.FMI3.modelIdentifier_valid
#audit axioms Rumoca.FMI3.modelIdentifier_injective
#audit axioms Rumoca.FMI3.functionPrefix_word
#audit axioms Rumoca.FMI3.sourcePrefix_correct
#audit axioms Rumoca.FMI3.sourcePrefix_of_chars
#audit axioms Rumoca.FMI3.modelIdentifiers_decode
#audit axioms Rumoca.FMI3.guard_correct
#audit axioms Rumoca.FMI3.guard_reference
#audit axioms Rumoca.FMI3.LifecycleGuard.mode_code_beq
#audit axioms Rumoca.FMI3.LifecycleGuard.modes_eval
#audit axioms Rumoca.FMI3.LifecycleGuard.eval_correct
#audit axioms Rumoca.FMI3.LifecycleGuard.reference
#audit axioms Rumoca.FMI3.LifecycleGuard.require_run
#audit axioms Rumoca.FMI3.LifecycleGuard.accept
#audit axioms Rumoca.FMI3.LifecycleGuard.reject_prefix
#audit axioms Rumoca.FMI3.LifecycleBodies.write_frame
#audit axioms Rumoca.FMI3.LifecycleBodies.write_mode
#audit axioms Rumoca.FMI3.LifecycleBodies.write_run
#audit axioms Rumoca.FMI3.LifecycleBodies.write_history
#audit axioms Rumoca.FMI3.LifecycleBodies.write_model
#audit axioms Rumoca.FMI3.LifecycleBodies.failure_mode_run
#audit axioms Rumoca.FMI3.LifecycleBodies.terminate_run
#audit axioms Rumoca.FMI3.LifecycleBodies.terminate_correct
#audit axioms Rumoca.FMI3.BodyEmbedding.body_closed
#audit axioms Rumoca.FMI3.RuntimePreprocessing.body_inputs
#audit axioms Rumoca.FMI3.RuntimePreprocessing.function_inputs
#audit axioms Rumoca.FMI3.RuntimePreprocessing.function_preprocessed
#audit axioms Rumoca.FMI3.AdapterPreprocessing.helpers_inputs
#audit axioms Rumoca.FMI3.AdapterPreprocessing.name_plain
#audit axioms Rumoca.FMI3.AdapterPreprocessing.declarations_stable
#audit axioms Rumoca.FMI3.AdapterPreprocessing.prefix_stable
#audit axioms Rumoca.FMI3.AdapterPreprocessing.render_stable
#audit axioms Rumoca.FMI3.AdapterPreprocessing.render_preprocessed
#audit axioms Rumoca.FMI3.BodyEmbedding.helpers_closed
#audit axioms Rumoca.FMI3.BodyEmbedding.runtime_behaviors
#audit axioms Rumoca.FMI3.BodyEmbedding.terminate_behaviors
#audit axioms Rumoca.FMI3.SetterScope.nonnull_equivalent
#audit axioms Rumoca.FMI3.SetterScope.null_equivalent
#audit axioms Rumoca.FMI3.SetterScope.emitted
#audit axioms Rumoca.FMI3.SetterScope.entry_run
#audit axioms Rumoca.FMI3.SetterScope.entry_reaches
#audit axioms Rumoca.FMI3.SetterScope.empty_behaviors
#audit axioms Rumoca.FMI3.SetterScope.null_behaviors
#audit axioms Rumoca.FMI3.ErrorBodies.failure_dispatch_run
#audit axioms Rumoca.FMI3.ErrorBodies.failure_log_arguments
#audit axioms Rumoca.FMI3.ErrorBodies.failure_silent_run
#audit axioms Rumoca.FMI3.ErrorBodies.failure_silent_correct
#audit axioms Rumoca.FMI3.ErrorBodies.nominals_reject_run
#audit axioms Rumoca.FMI3.ErrorBodies.nominals_reject_reaches
#audit axioms Rumoca.FMI3.StateProofs.null_instance_behaviors
#audit axioms Rumoca.FMI3.StateProofs.get_behaviors
#audit axioms Rumoca.FMI3.StateProofs.set_behaviors
#audit axioms Rumoca.FMI3.StateProofs.written_represents
#audit axioms Rumoca.FMI3.StateProofs.written_frame
#audit axioms Rumoca.FMI3.StateProofs.written_other_instance
#audit axioms Rumoca.FMI3.CallProofs.model_rhs_reaches
#audit axioms Rumoca.FMI3.CallProofs.model_advance_reaches
#audit axioms Rumoca.FMI3.CallProofs.model_advance_behaviors
#audit axioms Rumoca.FMI3.DerivativeProofs.get_reaches
#audit axioms Rumoca.FMI3.DerivativeProofs.get_behaviors
#audit axioms Rumoca.FMI3.TimeProofs.rejects_iff
#audit axioms Rumoca.FMI3.TimeProofs.guard_reference
#audit axioms Rumoca.FMI3.TimeProofs.guard_nonfinite
#audit axioms Rumoca.FMI3.TimeProofs.set_run
#audit axioms Rumoca.FMI3.TimeProofs.model_frame
#audit axioms Rumoca.FMI3.TimeProofs.set_behaviors
#audit axioms Rumoca.FMI3.HistoryProofs.put_run
#audit axioms Rumoca.FMI3.HistoryProofs.raise_run
#audit axioms Rumoca.FMI3.HistoryProofs.initial_correct
#audit axioms Rumoca.FMI3.HistoryProofs.event_correct
#audit axioms Rumoca.FMI3.HistoryProofs.completed_correct
#audit axioms Rumoca.FMI3.HistoryProofs.initial_frame
#audit axioms Rumoca.FMI3.HistoryProofs.event_frame
#audit axioms Rumoca.FMI3.HistoryProofs.completed_frame
#audit axioms Rumoca.FMI3.HistoryProofs.stored_guard_reference
#audit axioms Rumoca.FMI3.HistoryBodies.continuous_prefix
#audit axioms Rumoca.FMI3.HistoryBodies.zero_store
#audit axioms Rumoca.FMI3.HistoryBodies.zero_writable
#audit axioms Rumoca.FMI3.HistoryBodies.outputs_run
#audit axioms Rumoca.FMI3.HistoryBodies.event_reaches
#audit axioms Rumoca.FMI3.HistoryBodies.completed_reaches
#audit axioms Rumoca.FMI3.HistoryBodies.event_behaviors
#audit axioms Rumoca.FMI3.HistoryBodies.completed_behaviors
#audit axioms Rumoca.FMI3.HistoryBodies.event_frame
#audit axioms Rumoca.FMI3.HistoryBodies.completed_frame
#audit axioms Rumoca.FMI3.HistoryBodies.event_mode
#audit axioms Rumoca.FMI3.HistoryBodies.completed_mode
#audit axioms Rumoca.FMI3.HistoryBodies.completed_outputs
#audit axioms Rumoca.FMI3.HistoryBodies.event_model
#audit axioms Rumoca.FMI3.HistoryBodies.completed_model
#audit axioms Rumoca.FMI3.HistoryBodies.event_correct
#audit axioms Rumoca.FMI3.HistoryBodies.completed_correct
#audit axioms Rumoca.FMI3.InitializationBodies.exit_run
#audit axioms Rumoca.FMI3.InitializationBodies.exit_frame
#audit axioms Rumoca.FMI3.InitializationBodies.exit_mode
#audit axioms Rumoca.FMI3.InitializationBodies.exit_history
#audit axioms Rumoca.FMI3.InitializationBodies.exit_model
#audit axioms Rumoca.FMI3.InitializationBodies.exit_behaviors
#audit axioms Rumoca.FMI3.InitializationBodies.exit_correct
#audit axioms Rumoca.FMI3.InitializationEntry.rejects_iff
#audit axioms Rumoca.FMI3.InitializationEntry.guard_eval
#audit axioms Rumoca.FMI3.InitializationEntry.guard_reference
#audit axioms Rumoca.FMI3.InitializationEntry.prefix_run
#audit axioms Rumoca.FMI3.InitializationEntry.body_reaches
#audit axioms Rumoca.FMI3.InitializationEntry.frame
#audit axioms Rumoca.FMI3.InitializationEntry.stored
#audit axioms Rumoca.FMI3.InitializationEntry.model
#audit axioms Rumoca.FMI3.InitializationEntry.mode
#audit axioms Rumoca.FMI3.InitializationEntry.stop
#audit axioms Rumoca.FMI3.InitializationEntry.time_guard
#audit axioms Rumoca.FMI3.InitializationEntry.behaviors
#audit axioms Rumoca.FMI3.InitializationEntry.correct
#audit axioms Rumoca.FMI3.InitializationEntry.then_exit

#audit axioms Rumoca.FMI3.Version.call_reaches
#audit axioms Rumoca.FMI3.Version.call_behaviors
#audit axioms Rumoca.FMI3.Version.returned_bytes
#audit axioms Rumoca.FMI3.Version.collected
#audit axioms Rumoca.FMI3.Version.literal_bound
#audit axioms Rumoca.FMI3.Version.prepared_correct
#audit axioms Rumoca.FMI3.Version.function_tokenization
#audit axioms Rumoca.FMI3.Version.rendered_contract
#audit axioms Rumoca.FMI3.Build.decode_version
#audit axioms Rumoca.FMI3.Version.metadata_correct

#audit axioms Rumoca.FMI3.Logging.arguments_converted
#audit axioms Rumoca.FMI3.Logging.failure_prefix
#audit axioms Rumoca.FMI3.Logging.failure_behaviors
#audit axioms Rumoca.FMI3.Logging.execution_correct
#audit axioms Rumoca.FMI3.Logging.category_collected
#audit axioms Rumoca.FMI3.Logging.prepared_correct
#audit axioms Rumoca.FMI3.Logging.rendered_contract
#audit axioms Rumoca.FMI3.Logging.metadata_correct
#audit axioms Rumoca.FMI3.LiteralPreparation.rendered_helper
#audit axioms Rumoca.FMI3.LiteralPreparation.text_bound

#audit axioms Rumoca.FMI3.LiteralPreparation.event_lowering_behaviors
#audit axioms Rumoca.FMI3.LiteralPreparation.event_contract

#audit axioms Rumoca.FMI3.Logging.failure_dispatch_reaches
#audit axioms Rumoca.FMI3.Logging.failure_resume_reaches
#audit axioms Rumoca.FMI3.Logging.failure_all_behaviors
#audit axioms Rumoca.FMI3.Logging.failure_silent_behaviors
#audit axioms Rumoca.FMI3.Logging.all_execution_correct
#audit axioms Rumoca.FMI3.Logging.all_prepared_correct
#audit axioms Rumoca.FMI3.Logging.AllExecutionContract.determined
#audit axioms Rumoca.FMI3.Logging.AllPreparedContract.determined
#audit axioms Rumoca.FMI3.Logging.silent_prepared_correct

#audit axioms Rumoca.FMI3.Logging.failure_statement_entry
#audit axioms Rumoca.FMI3.Logging.failure_statement_all_behaviors
#audit axioms Rumoca.FMI3.Nominals.reject_dispatch
#audit axioms Rumoca.FMI3.Nominals.reject_all_behaviors
#audit axioms Rumoca.FMI3.Logging.failure_statement_silent_behaviors
#audit axioms Rumoca.FMI3.Nominals.reject_silent_behaviors
#audit axioms Rumoca.FMI3.Nominals.body_run
#audit axioms Rumoca.FMI3.Nominals.call_behaviors
#audit axioms Rumoca.FMI3.Nominals.frame
#audit axioms Rumoca.FMI3.Nominals.stored
#audit axioms Rumoca.FMI3.Nominals.null_parameters
#audit axioms Rumoca.FMI3.Nominals.null_body
#audit axioms Rumoca.FMI3.Nominals.null_behaviors
#audit axioms Rumoca.FMI3.Nominals.invalid_body
#audit axioms Rumoca.FMI3.Nominals.invalid_dispatch
#audit axioms Rumoca.FMI3.Nominals.invalid_all_behaviors
#audit axioms Rumoca.FMI3.Nominals.invalid_silent_behaviors
#audit axioms Rumoca.FMI3.NominalMetadata.described_nominals
#audit axioms Rumoca.FMI3.NominalMetadata.default_positive
#audit axioms Rumoca.FMI3.NominalMetadata.artifact_nominals
#audit axioms Rumoca.FMI3.Nominals.failure_message_collected
#audit axioms Rumoca.FMI3.Nominals.failure_all_behaviors
#audit axioms Rumoca.FMI3.Nominals.failure_silent_behaviors
#audit axioms Rumoca.FMI3.Nominals.failure_execution_correct
#audit axioms Rumoca.FMI3.Nominals.quiet_execution_correct
#audit axioms Rumoca.FMI3.Nominals.silent_execution_correct
#audit axioms Rumoca.FMI3.Nominals.prepared_correct
#audit axioms Rumoca.FMI3.Nominals.rendered_contract
#audit axioms Rumoca.FMI3.Nominals.query_cases
#audit axioms Rumoca.FMI3.Nominals.failure_cases_disjoint
#audit axioms Rumoca.FMI3.Nominals.stored_default

#audit axioms Rumoca.FMI3.GuardedCalls.rejected_prefix
#audit axioms Rumoca.FMI3.GuardedCalls.rejected_all_behaviors
#audit axioms Rumoca.FMI3.GuardedCalls.rejected_silent_behaviors
#audit axioms Rumoca.FMI3.GuardedCalls.null_body
#audit axioms Rumoca.FMI3.GuardedCalls.null_behaviors
#audit axioms Rumoca.FMI3.ScalarAccess.invalid_run
#audit axioms Rumoca.FMI3.ScalarAccess.valid_run
#audit axioms Rumoca.FMI3.StateCalls.Events.get_behaviors
#audit axioms Rumoca.FMI3.StateCalls.Events.set_behaviors
#audit axioms Rumoca.FMI3.StateCalls.Entry.parameters_bound
#audit axioms Rumoca.FMI3.StateCalls.Entry.parameters_valid
#audit axioms Rumoca.FMI3.StateCalls.Entry.body_eq
#audit axioms Rumoca.FMI3.StateCalls.Entry.null_behaviors
#audit axioms Rumoca.FMI3.StateCalls.Entry.rejected_all_behaviors
#audit axioms Rumoca.FMI3.StateCalls.Entry.rejected_silent_behaviors
#audit axioms Rumoca.FMI3.GuardedCalls.FailurePrefix.all_behaviors
#audit axioms Rumoca.FMI3.GuardedCalls.FailurePrefix.silent_behaviors
#audit axioms Rumoca.FMI3.StateCalls.Entry.invalid_run
#audit axioms Rumoca.FMI3.StateCalls.Entry.invalid_prefix
#audit axioms Rumoca.FMI3.StateCalls.Entry.nonfinite_run
#audit axioms Rumoca.FMI3.StateCalls.Entry.nonfinite_prefix
#audit axioms Rumoca.FMI3.StateCalls.Entry.query_cases
#audit axioms Rumoca.FMI3.StateCalls.Entry.failure_unique
#audit axioms Rumoca.FMI3.StateCalls.Entry.failure_prefix
#audit axioms Rumoca.FMI3.StateCalls.failure_execution_correct
#audit axioms Rumoca.FMI3.StateCalls.silent_execution_correct
#audit axioms Rumoca.FMI3.StateCalls.quiet_execution_correct
#audit axioms Rumoca.FMI3.StateCalls.failure_message_collected
#audit axioms Rumoca.FMI3.StateCalls.prepared_correct
#audit axioms Rumoca.FMI3.StateCalls.rendered_contract
#audit axioms Rumoca.FMI3.StateMetadata.StateReference.unique
#audit axioms Rumoca.FMI3.StateMetadata.OrderedStates.unique
#audit axioms Rumoca.FMI3.StateMetadata.described_states
#audit axioms Rumoca.FMI3.StateMetadata.artifact_states
#audit axioms Rumoca.FMI3.StateCalls.QuietExecutionContract.get_refines
#audit axioms Rumoca.FMI3.StateCalls.QuietExecutionContract.set_refines

#audit axioms Rumoca.FMI3.LiteralPreparation.numerical_bound
#audit axioms Rumoca.FMI3.LiteralPreparation.numerical_program
#audit axioms Rumoca.FMI3.ModelRhs.parameters_bound
#audit axioms Rumoca.FMI3.ModelRhs.types_bound
#audit axioms Rumoca.FMI3.ModelRhs.call_numerical
#audit axioms Rumoca.FMI3.ModelRhs.reaches
#audit axioms Rumoca.FMI3.ModelRhs.behaviors
#audit axioms Rumoca.FMI3.ModelRhs.rendered_contract
#audit axioms Rumoca.FMI3.TensorModelRhs.reaches
#audit axioms Rumoca.FMI3.TensorModelRhs.behaviors
#audit axioms Rumoca.FMI3.TensorModelRhs.events_reaches
#audit axioms Rumoca.FMI3.TensorModelRhs.rendered_contract
#audit axioms Rumoca.FMI3.DerivativeCalls.parameters_bound
#audit axioms Rumoca.FMI3.DerivativeCalls.body_eq
#audit axioms Rumoca.FMI3.DerivativeCalls.accepted_run
#audit axioms Rumoca.FMI3.DerivativeCalls.enter_rhs
#audit axioms Rumoca.FMI3.DerivativeCalls.return_rhs
#audit axioms Rumoca.FMI3.DerivativeCalls.finish
#audit axioms Rumoca.FMI3.DerivativeCalls.reaches
#audit axioms Rumoca.FMI3.DerivativeCalls.behaviors
#audit axioms Rumoca.FMI3.DerivativeCalls.query_cases
#audit axioms Rumoca.FMI3.DerivativeCalls.failure_unique
#audit axioms Rumoca.FMI3.DerivativeCalls.null_behaviors
#audit axioms Rumoca.FMI3.DerivativeCalls.invalid_run
#audit axioms Rumoca.FMI3.DerivativeCalls.failure_prefix
#audit axioms Rumoca.FMI3.DerivativeCalls.failure_execution_correct
#audit axioms Rumoca.FMI3.DerivativeCalls.silent_execution_correct
#audit axioms Rumoca.FMI3.DerivativeCalls.quiet_execution_correct
#audit axioms Rumoca.FMI3.DerivativeCalls.failure_message_collected
#audit axioms Rumoca.FMI3.DerivativeCalls.prepared_correct
#audit axioms Rumoca.FMI3.DerivativeCalls.rendered_contract
#audit axioms Rumoca.FMI3.DerivativeCalls.QuietExecutionContract.get_refines
#audit axioms Rumoca.FMI3.DerivativeMetadata.EntryName.unique
#audit axioms Rumoca.FMI3.DerivativeMetadata.DerivativeReference.unique
#audit axioms Rumoca.FMI3.DerivativeMetadata.OrderedDerivatives.unique
#audit axioms Rumoca.FMI3.DerivativeMetadata.OrderedDerivatives.states
#audit axioms Rumoca.FMI3.DerivativeMetadata.described_derivatives
#audit axioms Rumoca.FMI3.DerivativeMetadata.artifact_derivatives

#audit axioms Rumoca.FMI3.ArrayAccess.getter_guard
#audit axioms Rumoca.FMI3.ArrayAccess.setter_guard
#audit axioms Rumoca.FMI3.ArrayAccess.run_guard
#audit axioms Rumoca.FMI3.GuardedCalls.FailureSite.all_behaviors
#audit axioms Rumoca.FMI3.GuardedCalls.FailureSite.silent_behaviors
#audit axioms Rumoca.FMI3.Float64Calls.getter_body
#audit axioms Rumoca.FMI3.Float64Calls.validation_closed
#audit axioms Rumoca.FMI3.Float64Calls.read_closed
#audit axioms Rumoca.FMI3.Float64Calls.parameters_bound
#audit axioms Rumoca.FMI3.Float64Calls.get_guard_run
#audit axioms Rumoca.FMI3.Float64Calls.reference_eval
#audit axioms Rumoca.FMI3.Float64Calls.validation_step
#audit axioms Rumoca.FMI3.Float64Calls.counter_reference_eval
#audit axioms Rumoca.FMI3.Float64Calls.validation_prefix
#audit axioms Rumoca.FMI3.Float64Calls.validation_reaches
#audit axioms Rumoca.FMI3.Float64Calls.validation_rejects
#audit axioms Rumoca.FMI3.Float64Calls.reference_cases
#audit axioms Rumoca.FMI3.Float64Calls.variable_code_unique
#audit axioms Rumoca.FMI3.Float64Calls.variable_of_valid
#audit axioms Rumoca.FMI3.Float64Calls.read_dispatch
#audit axioms Rumoca.FMI3.Float64Calls.output_address
#audit axioms Rumoca.FMI3.Float64Calls.derivative_call
#audit axioms Rumoca.FMI3.Float64Calls.output_return
#audit axioms Rumoca.FMI3.Float64Calls.read_iteration
#audit axioms Rumoca.FMI3.Float64Calls.outputValues_at
#audit axioms Rumoca.FMI3.Float64Calls.pending_output
#audit axioms Rumoca.FMI3.Float64Calls.write_next_output
#audit axioms Rumoca.FMI3.Float64Calls.references_written
#audit axioms Rumoca.FMI3.Float64Calls.state_written
#audit axioms Rumoca.FMI3.Float64Calls.time_written
#audit axioms Rumoca.FMI3.Float64Calls.selectReference_correct
#audit axioms Rumoca.FMI3.Float64Calls.read_reaches
#audit axioms Rumoca.FMI3.Float64Calls.get_reaches
#audit axioms Rumoca.FMI3.Float64Calls.get_behaviors
#audit axioms Rumoca.FMI3.Float64Calls.empty_get_reaches
#audit axioms Rumoca.FMI3.Float64Calls.empty_get_behaviors
#audit axioms Rumoca.FMI3.Float64Calls.null_get_behaviors
#audit axioms Rumoca.FMI3.Float64Calls.get_array_error_site
#audit axioms Rumoca.FMI3.Float64Calls.get_reference_error_site
#audit axioms Rumoca.FMI3.Float64Calls.query_cases
#audit axioms Rumoca.FMI3.Float64Calls.failure_unique
#audit axioms Rumoca.FMI3.Float64Calls.failure_site
#audit axioms Rumoca.FMI3.Float64Metadata.Lookup.unique
#audit axioms Rumoca.FMI3.Float64Metadata.described_variable
#audit axioms Rumoca.FMI3.Float64Metadata.described_reference
#audit axioms Rumoca.FMI3.Float64Metadata.artifact_variables
#audit axioms Rumoca.FMI3.Float64Calls.failure_execution_correct
#audit axioms Rumoca.FMI3.Float64Calls.silent_execution_correct
#audit axioms Rumoca.FMI3.Float64Calls.quiet_execution_correct
#audit axioms Rumoca.FMI3.Float64Calls.failure_message_collected
#audit axioms Rumoca.FMI3.Float64Calls.prepared_correct
#audit axioms Rumoca.FMI3.Float64Calls.rendered_contract
#audit axioms Rumoca.FMI3.Float64Calls.QuietExecutionContract.get_refines
#audit axioms Rumoca.FMI3.Float64Calls.metadata_selection

#audit axioms Rumoca.FMI3.Float64Set.body_eq
#audit axioms Rumoca.FMI3.Float64Set.values_eq
#audit axioms Rumoca.FMI3.Float64Set.validation_closed
#audit axioms Rumoca.FMI3.Float64Set.write_closed
#audit axioms Rumoca.FMI3.Float64Set.entry_run
#audit axioms Rumoca.FMI3.Float64Set.guard_run
#audit axioms Rumoca.FMI3.Float64Set.empty_behaviors
#audit axioms Rumoca.FMI3.Float64Set.null_behaviors
#audit axioms Rumoca.FMI3.Float64Set.valid_entry_iff
#audit axioms Rumoca.FMI3.Float64Set.wrong_reference_step
#audit axioms Rumoca.FMI3.Float64Set.finite_check_step
#audit axioms Rumoca.FMI3.Float64Set.validation_step
#audit axioms Rumoca.FMI3.Float64Set.counter_value_eval
#audit axioms Rumoca.FMI3.Float64Set.validation_prefix
#audit axioms Rumoca.FMI3.Float64Set.validation_reaches
#audit axioms Rumoca.FMI3.Float64Set.validation_rejects
#audit axioms Rumoca.FMI3.Float64Set.assigned_frame
#audit axioms Rumoca.FMI3.Float64Set.assigned_writable
#audit axioms Rumoca.FMI3.Float64Set.assigned_next
#audit axioms Rumoca.FMI3.Float64Set.assigned_reads
#audit axioms Rumoca.FMI3.Float64Set.write_step
#audit axioms Rumoca.FMI3.Float64Set.write_reaches
#audit axioms Rumoca.FMI3.Float64Set.bitsAt_inside
#audit axioms Rumoca.FMI3.Float64Set.snapshot_readable
#audit axioms Rumoca.FMI3.Float64Set.snapshot_valid
#audit axioms Rumoca.FMI3.Float64Set.set_reaches
#audit axioms Rumoca.FMI3.Float64Set.set_behaviors
#audit axioms Rumoca.FMI3.Float64Set.accepted_snapshot
#audit axioms Rumoca.FMI3.Float64Set.assigned_represents
#audit axioms Rumoca.FMI3.Float64Set.entry_cases
#audit axioms Rumoca.FMI3.Float64Set.query_cases
#audit axioms Rumoca.FMI3.Float64Set.failure_unique
#audit axioms Rumoca.FMI3.Float64Set.lifecycle_site
#audit axioms Rumoca.FMI3.Float64Set.array_site
#audit axioms Rumoca.FMI3.Float64Set.entry_site
#audit axioms Rumoca.FMI3.Float64Set.failure_site
#audit axioms Rumoca.FMI3.Float64SetMetadata.Writable.lookup
#audit axioms Rumoca.FMI3.Float64SetMetadata.Writable.unique
#audit axioms Rumoca.FMI3.Float64SetMetadata.described_state
#audit axioms Rumoca.FMI3.Float64SetMetadata.described_reference
#audit axioms Rumoca.FMI3.Float64SetMetadata.artifact_state
#audit axioms Rumoca.FMI3.Float64Set.failure_execution_correct
#audit axioms Rumoca.FMI3.Float64Set.silent_execution_correct
#audit axioms Rumoca.FMI3.Float64Set.quiet_execution_correct
#audit axioms Rumoca.FMI3.Float64Set.QuietExecutionContract.set_refines
#audit axioms Rumoca.FMI3.Float64Set.failure_message_collected
#audit axioms Rumoca.FMI3.Float64Set.prepared_correct
#audit axioms Rumoca.FMI3.Float64Set.rendered_contract
#audit axioms Rumoca.FMI3.Float64Set.metadata_selection

#audit axioms Rumoca.FMI3.InitializationCalls.rejects_finite
#audit axioms Rumoca.FMI3.InitializationCalls.finite_admissible
#audit axioms Rumoca.FMI3.InitializationCalls.rejects_iff
#audit axioms Rumoca.FMI3.InitializationCalls.parameters_bound
#audit axioms Rumoca.FMI3.InitializationCalls.finite_parameters
#audit axioms Rumoca.FMI3.InitializationCalls.guard_eval
#audit axioms Rumoca.FMI3.InitializationCalls.closed
#audit axioms Rumoca.FMI3.InitializationCalls.function_eq
#audit axioms Rumoca.FMI3.InitializationCalls.guard_run
#audit axioms Rumoca.FMI3.InitializationCalls.tail_run
#audit axioms Rumoca.FMI3.InitializationCalls.body_run
#audit axioms Rumoca.FMI3.InitializationCalls.call_behaviors
#audit axioms Rumoca.FMI3.InitializationCalls.stored
#audit axioms Rumoca.FMI3.InitializationCalls.query_cases
#audit axioms Rumoca.FMI3.InitializationCalls.failure_unique
#audit axioms Rumoca.FMI3.InitializationCalls.null_behaviors
#audit axioms Rumoca.FMI3.InitializationCalls.lifecycle_prefix
#audit axioms Rumoca.FMI3.InitializationCalls.arguments_prefix
#audit axioms Rumoca.FMI3.InitializationCalls.failure_prefix
#audit axioms Rumoca.FMI3.InitializationCalls.failure_execution_correct
#audit axioms Rumoca.FMI3.InitializationCalls.silent_execution_correct
#audit axioms Rumoca.FMI3.InitializationCalls.time_guard
#audit axioms Rumoca.FMI3.InitializationExit.body
#audit axioms Rumoca.FMI3.InitializationExit.closed
#audit axioms Rumoca.FMI3.InitializationExit.finite_parameters
#audit axioms Rumoca.FMI3.InitializationExit.parameters_bound
#audit axioms Rumoca.FMI3.InitializationExit.call_behaviors
#audit axioms Rumoca.FMI3.InitializationExit.null_behaviors
#audit axioms Rumoca.FMI3.InitializationExit.failure_prefix
#audit axioms Rumoca.FMI3.InitializationCalls.entered_kind
#audit axioms Rumoca.FMI3.InitializationCalls.entered_mode
#audit axioms Rumoca.FMI3.InitializationCalls.exited_frame
#audit axioms Rumoca.FMI3.InitializationCalls.exited_time_guard
#audit axioms Rumoca.FMI3.InitializationExit.failure_execution_correct
#audit axioms Rumoca.FMI3.InitializationExit.silent_execution_correct
#audit axioms Rumoca.FMI3.InitializationCalls.quiet_execution_correct
#audit axioms Rumoca.FMI3.InitializationCalls.QuietExecutionContract.initialize

#audit axioms Rumoca.FMI3.InitializationCalls.failure_message_collected
#audit axioms Rumoca.FMI3.InitializationCalls.PreparedContract.quiet
#audit axioms Rumoca.FMI3.InitializationCalls.prepared_correct
#audit axioms Rumoca.FMI3.InitializationCalls.rendered_contract

#audit axioms Rumoca.FMI3.StaticSlots.reserve_iff
#audit axioms Rumoca.FMI3.StaticSlots.reserve_busy
#audit axioms Rumoca.FMI3.StaticSlots.reserve_frame
#audit axioms Rumoca.FMI3.StaticSlots.cannot_reserve_twice
#audit axioms Rumoca.FMI3.StaticSlots.consecutive_distinct
#audit axioms Rumoca.FMI3.StaticSlots.full_iff
#audit axioms Rumoca.FMI3.StaticSlots.release_iff
#audit axioms Rumoca.FMI3.StaticSlots.release_vacant
#audit axioms Rumoca.FMI3.StaticSlots.release_frame
#audit axioms Rumoca.FMI3.StaticSlots.release_after_reserve
#audit axioms Rumoca.FMI3.StaticSlots.reusable
#audit axioms Rumoca.FMI3.SlotOwners.reserve_refines
#audit axioms Rumoca.FMI3.SlotOwners.release_refines
#audit axioms Rumoca.FMI3.SlotOwners.only_owner_releases
#audit axioms Rumoca.FMI3.SlotOwners.reserved_excludes
#audit axioms Rumoca.FMI3.SlotOwners.initialized
#audit axioms Rumoca.FMI3.SlotOwners.exchange_reserves
#audit axioms Rumoca.FMI3.SlotOwners.exchange_busy
#audit axioms Rumoca.FMI3.SlotOwners.write_releases
#audit axioms Rumoca.FMI3.SlotOwners.internal_preserves
#audit axioms Rumoca.FMI3.SlotExecution.internal
#audit axioms Rumoca.FMI3.SlotExecution.reaches_preserves
#audit axioms Rumoca.FMI3.SlotExecution.reaches_executes
#audit axioms Rumoca.FMI3.StaticSlots.update_commutes
#audit axioms Rumoca.FMI3.StaticSlots.findFree_sound
#audit axioms Rumoca.FMI3.StaticSlots.findFree_none_iff
#audit axioms Rumoca.FMI3.StaticSlots.findFree_exhausted
#audit axioms Rumoca.FMI3.StaticSlots.findFree_reserves

#audit axioms Rumoca.FMI3.AtomicSlots.initialized
#audit axioms Rumoca.FMI3.AtomicSlots.exchange_exists
#audit axioms Rumoca.FMI3.AtomicSlots.reserve_corresponds
#audit axioms Rumoca.FMI3.AtomicSlots.release_exists
#audit axioms Rumoca.FMI3.AtomicSlots.scan_ready
#audit axioms Rumoca.FMI3.AtomicSlots.scan_reserves
#audit axioms Rumoca.FMI3.AtomicSlots.scan_exhausted

#audit axioms Rumoca.FMI3.Identity.parameters_bound
#audit axioms Rumoca.FMI3.Identity.initialization
#audit axioms Rumoca.FMI3.Identity.measure_equivalence
#audit axioms Rumoca.FMI3.Identity.prefix_equivalence
#audit axioms Rumoca.FMI3.Identity.comparison_equivalence
#audit axioms Rumoca.FMI3.Identity.accepted_iff
#audit axioms Rumoca.FMI3.Identity.accepted_span
#audit axioms Rumoca.FMI3.Identity.call_equivalence
#audit axioms Rumoca.FMI3.Identity.call_correct
#audit axioms Rumoca.FMI3.Identity.guards_reaches
#audit axioms Rumoca.FMI3.Identity.null_call_equivalence
#audit axioms Rumoca.FMI3.Identity.null_call_correct
#audit axioms Rumoca.FMI3.Identity.Printer.function_printable_in
#audit axioms Rumoca.FMI3.Identity.Printer.function_denotes
#audit axioms Rumoca.FMI3.Identity.Printer.function_tokenization
#audit axioms Rumoca.FMI3.Identity.library_undefined
#audit axioms Rumoca.FMI3.Identity.helper_defined
#audit axioms Rumoca.FMI3.Identity.bindings_exist
#audit axioms Rumoca.FMI3.Identity.execution_correct
#audit axioms Rumoca.FMI3.Identity.rendered_contract
#audit axioms Rumoca.FMI3.Identity.constants_collected
#audit axioms Rumoca.FMI3.Identity.constants_ready
#audit axioms Rumoca.FMI3.Identity.prepared_equivalence
#audit axioms Rumoca.FMI3.Identity.factory_enters
#audit axioms Rumoca.FMI3.Identity.factory_resumes
#audit axioms Rumoca.FMI3.Identity.factory_validates
#audit axioms Rumoca.FMI3.Identity.factory_null
#audit axioms Rumoca.FMI3.NameParts.nonzero_ascii
#audit axioms Rumoca.FMI3.Identity.token_content

#audit axioms Rumoca.FMI3.FactoryRejection.identity_guard
#audit axioms Rumoca.FMI3.FactoryRejection.dispatch
#audit axioms Rumoca.FMI3.FactoryRejection.return_null
#audit axioms Rumoca.FMI3.FactoryRejection.callback_entry
#audit axioms Rumoca.FMI3.FactoryRejection.silent_equivalence
#audit axioms Rumoca.FMI3.FactoryRejection.all_behaviors
#audit axioms Rumoca.FMI3.FactoryArguments.scope
#audit axioms Rumoca.FMI3.FactoryArguments.ready
#audit axioms Rumoca.FMI3.FactoryArguments.arguments_converted
#audit axioms Rumoca.FMI3.FactoryArguments.parameters_bound
#audit axioms Rumoca.FMI3.FactoryArguments.call_entry
#audit axioms Rumoca.FMI3.FactoryEntry.coSimulation_guard
#audit axioms Rumoca.FMI3.FactoryEntry.validation_entry
#audit axioms Rumoca.FMI3.FactoryNull.reaches_rejection
#audit axioms Rumoca.FMI3.FactoryNull.silent_behaviors
#audit axioms Rumoca.FMI3.FactoryNull.logged_behaviors
#audit axioms Rumoca.FMI3.FactoryValidation.admission_equivalence
#audit axioms Rumoca.FMI3.FactoryValidation.rejected_silent
#audit axioms Rumoca.FMI3.FactoryValidation.rejected_logged
#audit axioms Rumoca.FMI3.FactoryUnsupported.rejection_entry
#audit axioms Rumoca.FMI3.FactoryUnsupported.silent_behaviors
#audit axioms Rumoca.FMI3.FactoryUnsupported.logged_behaviors
#audit axioms Rumoca.FMI3.FactoryLiterals.collected
#audit axioms Rumoca.FMI3.FactoryLiterals.prepared
#audit axioms Rumoca.FMI3.FactoryLiterals.preserved
#audit axioms Rumoca.FMI3.FactoryAdmission.execution_correct
#audit axioms Rumoca.FMI3.FactoryAdmission.prepared_correct
#audit axioms Rumoca.FMI3.FactoryAdmission.rendered_contract
#audit axioms Rumoca.FMI3.InstanceInitialization.run_initialization
#audit axioms Rumoca.FMI3.InstanceInitialization.frame
#audit axioms Rumoca.FMI3.InstanceInitialization.other_instance
#audit axioms Rumoca.FMI3.InstanceInitialization.storage_ready
#audit axioms Rumoca.FMI3.InstanceInitialization.reuse
#audit axioms Rumoca.FMI3.InstanceInitialization.initialized
#audit axioms Rumoca.FMI3.InstanceInitialization.run_return
#audit axioms Rumoca.FMI3.InstanceInitialization.return_reaches
#audit axioms Rumoca.FMI3.InstanceInitialization.complete
#audit axioms Rumoca.FMI3.InstanceInitialization.Storage.preserved
#audit axioms Rumoca.FMI3.InstanceInitialization.reserved_storage
#audit axioms Rumoca.FMI3.InstanceInitialization.initialized_owners
#audit axioms Rumoca.FMI3.StaticFactory.select_step
#audit axioms Rumoca.FMI3.StaticFactory.guard_step
#audit axioms Rumoca.FMI3.StaticFactory.selected_bindings
#audit axioms Rumoca.FMI3.StaticFactory.initialization_reaches
#audit axioms Rumoca.FMI3.StaticFactory.guarded_initialization
#audit axioms Rumoca.FMI3.StaticFactory.reserve_entry
#audit axioms Rumoca.FMI3.StaticFactory.reserve_resume
#audit axioms Rumoca.FMI3.StaticFactory.successful
#audit axioms Rumoca.FMI3.StaticFactory.constants_unchanged
#audit axioms Rumoca.FMI3.StaticFactory.types_unchanged
#audit axioms Rumoca.FMI3.StaticFactory.factory_scope
#audit axioms Rumoca.FMI3.StaticFactory.exhaustion_path
#audit axioms Rumoca.FMI3.StaticFactory.exhausted_silent
#audit axioms Rumoca.FMI3.StaticFactory.exhausted_logged
#audit axioms Rumoca.FMI3.StaticFactory.create_silent
#audit axioms Rumoca.FMI3.StaticFactory.create_logged
#audit axioms Rumoca.FMI3.StaticRelease.call_entry
#audit axioms Rumoca.FMI3.StaticRelease.guard_step
#audit axioms Rumoca.FMI3.StaticRelease.return_path
#audit axioms Rumoca.FMI3.StaticRelease.clear_entry
#audit axioms Rumoca.FMI3.StaticRelease.null_behaviors
#audit axioms Rumoca.FMI3.StaticRelease.occupied_behaviors
#audit axioms Rumoca.FMI3.StaticRelease.release_owned
#audit axioms Rumoca.FMI3.InstanceSlot.Storage.preserved
#audit axioms Rumoca.FMI3.InstanceSlot.store_index
#audit axioms Rumoca.FMI3.InstanceSlot.initialization_frame
#audit axioms Rumoca.FMI3.InstanceSlot.final_index
#audit axioms Rumoca.FMI3.InstanceSlot.metadata
#audit axioms Rumoca.FMI3.InstanceSlot.storage_ready
#audit axioms Rumoca.FMI3.InstanceSlot.initialized
#audit axioms Rumoca.FMI3.InstanceSlot.frame
#audit axioms Rumoca.FMI3.InstanceSlot.step
#audit axioms Rumoca.FMI3.InstanceSlot.return_reaches
#audit axioms Rumoca.FMI3.InstanceSlot.initialized_owners
#audit axioms Rumoca.FMI3.InstanceSlot.complete
#audit axioms Rumoca.FMI3.StaticFactory.successful_owned
#audit axioms Rumoca.FMI3.StaticFactory.Created.release
#audit axioms Rumoca.FMI3.StaticFactory.create_release
#audit axioms Rumoca.FMI3.FactoryArguments.base_types
#audit axioms Rumoca.FMI3.StaticFactory.factory_types
#audit axioms Rumoca.FMI3.StaticFactory.public_admission
#audit axioms Rumoca.FMI3.StaticFactory.public_create_silent
#audit axioms Rumoca.FMI3.StaticFactory.public_create_logged
#audit axioms Rumoca.FMI3.StaticFactory.public_create_release
#audit axioms Rumoca.FMI3.StaticFactory.public_rejected_silent
#audit axioms Rumoca.FMI3.StaticFactory.public_rejected_logged
#audit axioms Rumoca.FMI3.StaticFactory.Printer.signature_printable
#audit axioms Rumoca.FMI3.StaticFactory.Printer.factory_printable
#audit axioms Rumoca.FMI3.StaticFactory.Printer.release_printable
#audit axioms Rumoca.FMI3.StaticFactory.Printer.factory_denotes
#audit axioms Rumoca.FMI3.StaticFactory.Printer.factory_tokenization
#audit axioms Rumoca.FMI3.StaticFactory.Printer.release_denotes
#audit axioms Rumoca.FMI3.StaticFactory.Printer.release_tokenization
#audit axioms Rumoca.FMI3.StaticStorage.model_resolves
#audit axioms Rumoca.FMI3.StaticStorage.instance_resolves
#audit axioms Rumoca.FMI3.StaticStorage.records_mean
#audit axioms Rumoca.FMI3.StaticStorage.model_printable
#audit axioms Rumoca.FMI3.StaticStorage.instance_printable
#audit axioms Rumoca.FMI3.StaticStorage.instances_printable
#audit axioms Rumoca.FMI3.StaticStorage.flags_printable
#audit axioms Rumoca.FMI3.StaticStorage.count_printable
#audit axioms Rumoca.FMI3.StaticStorage.printed
#audit axioms Rumoca.FMI3.StaticStorage.initial_member
#audit axioms Rumoca.FMI3.StaticStorage.initial_fields
#audit axioms Rumoca.FMI3.StaticStorage.initial_flags
#audit axioms Rumoca.FMI3.StaticStorage.initial_ready
#audit axioms Rumoca.FMI3.StaticStorage.initial_owners
#audit axioms Rumoca.FMI3.StaticStorage.symbol_bindings
#audit axioms Rumoca.FMI3.StaticStorage.capacity_conversion
#audit axioms Rumoca.FMI3.StaticStorage.instances_fresh
#audit axioms Rumoca.FMI3.StaticStorage.flags_fresh
#audit axioms Rumoca.FMI3.StaticStorage.initial_preserves
#audit axioms Rumoca.FMI3.StaticStorage.declarations_initialize
#audit axioms Rumoca.FMI3.StaticStorage.initial_create_release
#audit axioms Rumoca.FMI3.StaticRuntime.factory_definition
#audit axioms Rumoca.FMI3.StaticRuntime.release_definition
#audit axioms Rumoca.FMI3.StaticRuntime.factory_bound
#audit axioms Rumoca.FMI3.StaticRuntime.release_bound
#audit axioms Rumoca.FMI3.StaticRuntime.reservation_bound
#audit axioms Rumoca.FMI3.StaticRuntime.identity_bound
#audit axioms Rumoca.FMI3.StaticRuntime.external_undefined
#audit axioms Rumoca.FMI3.StaticRuntime.library_names
#audit axioms Rumoca.FMI3.StaticRuntime.bindings_exist
#audit axioms Rumoca.FMI3.StaticRuntime.declarations_located
#audit axioms Rumoca.FMI3.StaticRuntime.initial_execution
#audit axioms Rumoca.FMI3.StaticRuntime.rendered_contract
#audit axioms Rumoca.FMI3.StaticRuntime.FunctionContract.release_defined
#audit axioms Rumoca.FMI3.StaticFactory.capacity_message_collected
#audit axioms Rumoca.FMI3.StaticFactory.capacity_message_prepared
#audit axioms Rumoca.FMI3.StaticInitialization.interface_types
#audit axioms Rumoca.FMI3.StaticInitialization.enter_agrees
#audit axioms Rumoca.FMI3.StaticInitialization.exit_agrees
#audit axioms Rumoca.FMI3.StaticInitialization.entry_storage
#audit axioms Rumoca.FMI3.StaticInitialization.enter_call
#audit axioms Rumoca.FMI3.StaticInitialization.exit_call
#audit axioms Rumoca.FMI3.StaticInitialization.null_call
#audit axioms Rumoca.FMI3.StaticInitialization.quiet_correct
#audit axioms Rumoca.FMI3.StaticInitialization.exited_metadata
#audit axioms Rumoca.FMI3.StaticInitialization.exited_owners

#audit axioms Rumoca.FMI3.StaticErrors.helper_agrees
#audit axioms Rumoca.FMI3.StaticErrors.helper_parameters
#audit axioms Rumoca.FMI3.StaticErrors.dispatch_reaches
#audit axioms Rumoca.FMI3.StaticErrors.resume_reaches
#audit axioms Rumoca.FMI3.StaticErrors.helper_all_behaviors
#audit axioms Rumoca.FMI3.StaticErrors.helper_silent_behaviors
#audit axioms Rumoca.FMI3.StaticErrors.helper_silent_reaches
#audit axioms Rumoca.FMI3.StaticErrors.failure_prefix
#audit axioms Rumoca.FMI3.StaticErrors.statement_entry
#audit axioms Rumoca.FMI3.StaticErrors.failure_all_behaviors
#audit axioms Rumoca.FMI3.StaticErrors.failure_silent_behaviors
#audit axioms Rumoca.FMI3.StaticInitialization.enter_silent_correct
#audit axioms Rumoca.FMI3.StaticInitialization.enter_logged_correct
#audit axioms Rumoca.FMI3.StaticInitialization.exit_silent_correct
#audit axioms Rumoca.FMI3.StaticInitialization.exit_logged_correct
#audit axioms Rumoca.FMI3.StaticInitialization.prepared_correct
#audit axioms Rumoca.FMI3.StaticErrors.logging_cases
#audit axioms Rumoca.FMI3.StaticErrors.helper_suppressed_reaches
#audit axioms Rumoca.FMI3.StaticErrors.failure_suppressed_behaviors
#audit axioms Rumoca.FMI3.StaticInitialization.enter_suppressed_correct
#audit axioms Rumoca.FMI3.StaticInitialization.exit_suppressed_correct

#audit axioms Rumoca.FMI3.StaticReset.body_agrees
#audit axioms Rumoca.FMI3.StaticReset.call_behaviors
#audit axioms Rumoca.FMI3.StaticReset.null_behaviors
#audit axioms Rumoca.FMI3.StaticReset.entry_storage
#audit axioms Rumoca.FMI3.StaticReset.kind_value
#audit axioms Rumoca.FMI3.StaticReset.metadata
#audit axioms Rumoca.FMI3.StaticReset.record_frame
#audit axioms Rumoca.FMI3.StaticReset.other_instance
#audit axioms Rumoca.FMI3.StaticReset.owners
#audit axioms Rumoca.FMI3.StaticReset.restarted_frame
#audit axioms Rumoca.FMI3.StaticReset.restarted_other_instance
#audit axioms Rumoca.FMI3.StaticReset.restarted_owners
#audit axioms Rumoca.FMI3.StaticReset.execution_correct

#audit axioms Rumoca.FMI3.Termination.body
#audit axioms Rumoca.FMI3.Termination.closed
#audit axioms Rumoca.FMI3.Termination.body_agrees
#audit axioms Rumoca.FMI3.Termination.call_behaviors
#audit axioms Rumoca.FMI3.Termination.null_behaviors
#audit axioms Rumoca.FMI3.Termination.failure_prefix
#audit axioms Rumoca.FMI3.Termination.quiet_correct
#audit axioms Rumoca.FMI3.Termination.suppressed_correct
#audit axioms Rumoca.FMI3.Termination.logged_correct
#audit axioms Rumoca.FMI3.Termination.message_collected
#audit axioms Rumoca.FMI3.Termination.prepared_correct
#audit axioms Rumoca.FMI3.Termination.rendered_contract

#audit axioms Rumoca.FMI3.Termination.lease_metadata
#audit axioms Rumoca.FMI3.Termination.lease_owners
#audit axioms Rumoca.FMI3.Termination.terminate_release

#audit axioms Rumoca.FMI3.TimeCalls.body_agrees
#audit axioms Rumoca.FMI3.TimeCalls.parameters_bound
#audit axioms Rumoca.FMI3.TimeCalls.bit_cases
#audit axioms Rumoca.FMI3.TimeCalls.query_cases
#audit axioms Rumoca.FMI3.TimeCalls.failure_unique
#audit axioms Rumoca.FMI3.TimeCalls.call_behaviors
#audit axioms Rumoca.FMI3.TimeCalls.null_behaviors
#audit axioms Rumoca.FMI3.TimeCalls.lifecycle_prefix
#audit axioms Rumoca.FMI3.TimeCalls.nonfinite_prefix
#audit axioms Rumoca.FMI3.TimeCalls.window_rejected_eval
#audit axioms Rumoca.FMI3.TimeCalls.failure_prefix
#audit axioms Rumoca.FMI3.TimeCalls.quiet_correct
#audit axioms Rumoca.FMI3.TimeCalls.suppressed_correct
#audit axioms Rumoca.FMI3.TimeCalls.logged_correct
#audit axioms Rumoca.FMI3.TimeCalls.message_collected
#audit axioms Rumoca.FMI3.TimeCalls.prepared_correct
#audit axioms Rumoca.FMI3.TimeCalls.rendered_contract
#audit axioms Rumoca.FMI3.TimeCalls.admitted_finite
#audit axioms Rumoca.FMI3.TimeCalls.failure_excludes_success
#audit axioms Rumoca.FMI3.TimeCalls.frame
#audit axioms Rumoca.FMI3.TimeCalls.bounds_after
#audit axioms Rumoca.FMI3.TimeCalls.history_call

#audit axioms Rumoca.FMI3.CompletedCalls.body
#audit axioms Rumoca.FMI3.CompletedCalls.body_agrees
#audit axioms Rumoca.FMI3.CompletedCalls.bounds_stored
#audit axioms Rumoca.FMI3.CompletedCalls.call_behaviors
#audit axioms Rumoca.FMI3.CompletedCalls.failure_prefix
#audit axioms Rumoca.FMI3.CompletedCalls.failure_unique
#audit axioms Rumoca.FMI3.CompletedCalls.history_call
#audit axioms Rumoca.FMI3.CompletedCalls.lifecycle_prefix
#audit axioms Rumoca.FMI3.CompletedCalls.logged_correct
#audit axioms Rumoca.FMI3.CompletedCalls.message_collected
#audit axioms Rumoca.FMI3.CompletedCalls.null_behaviors
#audit axioms Rumoca.FMI3.CompletedCalls.output_prefix
#audit axioms Rumoca.FMI3.CompletedCalls.parameters_bound
#audit axioms Rumoca.FMI3.CompletedCalls.prepared_correct
#audit axioms Rumoca.FMI3.CompletedCalls.query_cases
#audit axioms Rumoca.FMI3.CompletedCalls.quiet_correct
#audit axioms Rumoca.FMI3.CompletedCalls.rendered_contract
#audit axioms Rumoca.FMI3.CompletedCalls.suppressed_correct
#audit axioms Rumoca.FMI3.DiscreteCalls.body
#audit axioms Rumoca.FMI3.DiscreteCalls.body_agrees
#audit axioms Rumoca.FMI3.DiscreteCalls.body_run
#audit axioms Rumoca.FMI3.DiscreteCalls.call_behaviors
#audit axioms Rumoca.FMI3.DiscreteCalls.failure_prefix
#audit axioms Rumoca.FMI3.DiscreteCalls.failure_unique
#audit axioms Rumoca.FMI3.DiscreteCalls.frame
#audit axioms Rumoca.FMI3.DiscreteCalls.history_call
#audit axioms Rumoca.FMI3.DiscreteCalls.instance_frame
#audit axioms Rumoca.FMI3.DiscreteCalls.lifecycle_prefix
#audit axioms Rumoca.FMI3.DiscreteCalls.logged_correct
#audit axioms Rumoca.FMI3.DiscreteCalls.message_collected
#audit axioms Rumoca.FMI3.DiscreteCalls.nonnull_arguments
#audit axioms Rumoca.FMI3.DiscreteCalls.null_behaviors
#audit axioms Rumoca.FMI3.DiscreteCalls.output_bound
#audit axioms Rumoca.FMI3.DiscreteCalls.output_prefix
#audit axioms Rumoca.FMI3.DiscreteCalls.outputs_compatible
#audit axioms Rumoca.FMI3.DiscreteCalls.outputs_ready
#audit axioms Rumoca.FMI3.DiscreteCalls.parameters_bound
#audit axioms Rumoca.FMI3.DiscreteCalls.prepared_correct
#audit axioms Rumoca.FMI3.DiscreteCalls.query_cases
#audit axioms Rumoca.FMI3.DiscreteCalls.quiet_correct
#audit axioms Rumoca.FMI3.DiscreteCalls.rendered_contract
#audit axioms Rumoca.FMI3.DiscreteCalls.returned_outputs
#audit axioms Rumoca.FMI3.DiscreteCalls.suppressed_correct
#audit axioms Rumoca.FMI3.DiscreteCalls.tail_outputs
#audit axioms Rumoca.FMI3.EventEntry.allowed
#audit axioms Rumoca.FMI3.EventEntry.body
#audit axioms Rumoca.FMI3.EventEntry.body_agrees
#audit axioms Rumoca.FMI3.EventEntry.bounds_stored
#audit axioms Rumoca.FMI3.EventEntry.call_behaviors
#audit axioms Rumoca.FMI3.EventEntry.continuous_run
#audit axioms Rumoca.FMI3.EventEntry.failure_prefix
#audit axioms Rumoca.FMI3.EventEntry.frame
#audit axioms Rumoca.FMI3.EventEntry.history_call
#audit axioms Rumoca.FMI3.EventEntry.logged_correct
#audit axioms Rumoca.FMI3.EventEntry.message_collected
#audit axioms Rumoca.FMI3.EventEntry.mode_stored
#audit axioms Rumoca.FMI3.EventEntry.model_stored
#audit axioms Rumoca.FMI3.EventEntry.null_behaviors
#audit axioms Rumoca.FMI3.EventEntry.prepared_correct
#audit axioms Rumoca.FMI3.EventEntry.query_cases
#audit axioms Rumoca.FMI3.EventEntry.quiet_correct
#audit axioms Rumoca.FMI3.EventEntry.rendered_contract
#audit axioms Rumoca.FMI3.EventEntry.represents
#audit axioms Rumoca.FMI3.EventEntry.stored
#audit axioms Rumoca.FMI3.EventEntry.suppressed_correct

#audit axioms Rumoca.FMI3.MEHistory.Buffers.writable
#audit axioms Rumoca.FMI3.MEHistory.Buffers.transport
#audit axioms Rumoca.FMI3.MEHistory.Buffers.Outside.field
#audit axioms Rumoca.FMI3.MEHistory.Buffers.zero
#audit axioms Rumoca.FMI3.MEHistory.Buffers.completed
#audit axioms Rumoca.FMI3.MEHistory.Buffers.discrete
#audit axioms Rumoca.FMI3.MEHistory.step
#audit axioms Rumoca.FMI3.MEHistory.trace
#audit axioms Rumoca.FMI3.MEHistory.continuous_requires_iteration
#audit axioms Rumoca.FMI3.MEHistory.initial_requires_iteration
#audit axioms Rumoca.FMI3.MEHistory.action_frame
#audit axioms Rumoca.FMI3.MEHistory.trace_frame

#audit axioms Rumoca.FMI3.MEHistory.initialized_stored
#audit axioms Rumoca.FMI3.MEHistory.initialize_trace
#audit axioms Rumoca.FMI3.HistoryProofs.write_atomic
#audit axioms Rumoca.FMI3.HistoryProofs.raise_atomic
#audit axioms Rumoca.FMI3.HistoryProofs.event_atomic
#audit axioms Rumoca.FMI3.HistoryProofs.completed_atomic
#audit axioms Rumoca.FMI3.MEHistory.action_atomic
#audit axioms Rumoca.FMI3.MEHistory.trace_atomic_frame
#audit axioms Rumoca.FMI3.MEHistory.Action.next_live
#audit axioms Rumoca.FMI3.MEHistory.ReferenceTrace.live
#audit axioms Rumoca.FMI3.MEHistory.ReferenceState.Live.terminate
#audit axioms Rumoca.FMI3.MEHistory.slot_outside
#audit axioms Rumoca.FMI3.MEHistory.release_correct

#audit axioms Rumoca.FMI3.StaticFactory.public_create_owned
#audit axioms Rumoca.FMI3.SlotOwners.release_reserved_restore
#audit axioms Rumoca.FMI3.MEHistory.Buffers.storage_preserved
#audit axioms Rumoca.FMI3.MEHistory.initialize_release

#audit axioms Rumoca.FMI3.ModelAdvance.advance_parameters
#audit axioms Rumoca.FMI3.ModelAdvance.advance_reaches
#audit axioms Rumoca.FMI3.ModelAdvance.advance_behaviors
#audit axioms Rumoca.FMI3.ModelAdvance.static_types
#audit axioms Rumoca.FMI3.ModelAdvance.prepared_behaviors
#audit axioms Rumoca.FMI3.ModelAdvance.written_frame

#audit axioms Rumoca.FMI3.StepAdmission.duration_count
#audit axioms Rumoca.FMI3.StepAdmission.count_unique
#audit axioms Rumoca.FMI3.StepAdmission.duration_of_count
#audit axioms Rumoca.FMI3.StepAdmission.duration_checks
#audit axioms Rumoca.FMI3.StepAdmission.duration_sum
#audit axioms Rumoca.FMI3.StepAdmission.duration_progress
#audit axioms Rumoca.FMI3.StepAdvance.actual_tail
#audit axioms Rumoca.FMI3.StepAdvance.time_ne_state
#audit axioms Rumoca.FMI3.StepAdvance.reaches
#audit axioms Rumoca.FMI3.StepAdvance.written_frame
#audit axioms Rumoca.FMI3.StepAdvance.written_values

#audit axioms Rumoca.FMI3.RuntimeEnvironment.types_agree
#audit axioms Rumoca.FMI3.RuntimeEnvironment.time_body_agrees
#audit axioms Rumoca.FMI3.RuntimeEnvironment.time_call_behaviors
#audit axioms Rumoca.FMI3.RuntimeEnvironment.model_advance_behaviors
#audit axioms Rumoca.FMI3.RuntimeEnvironment.time_quiet

#audit axioms Rumoca.FMI3.StepGuards.stop_condition
#audit axioms Rumoca.FMI3.StepGuards.progress_condition
#audit axioms Rumoca.FMI3.StepGuards.grid_condition
#audit axioms Rumoca.FMI3.StepGuards.rounding_path
#audit axioms Rumoca.FMI3.StepGuards.clock_path
#audit axioms Rumoca.FMI3.StepGuards.grid_path
#audit axioms Rumoca.FMI3.StepGuards.actual_sections
#audit axioms Rumoca.FMI3.StepGuards.accepted_execution

#audit axioms Rumoca.FMI3.StepEntry.body
#audit axioms Rumoca.FMI3.StepEntry.parameters_bound
#audit axioms Rumoca.FMI3.StepEntry.lifecycle_run
#audit axioms Rumoca.FMI3.StepEntry.input_condition
#audit axioms Rumoca.FMI3.StepEntry.float_ne_boolean
#audit axioms Rumoca.FMI3.StepEntry.outputs_run
#audit axioms Rumoca.FMI3.StepEntry.output_frame
#audit axioms Rumoca.FMI3.StepEntry.output_instance
#audit axioms Rumoca.FMI3.StepEntry.ready_run
#audit axioms Rumoca.FMI3.StepEntry.null_call
#audit axioms Rumoca.FMI3.StepEntry.accepted_call
#audit axioms Rumoca.FMI3.StepEntry.output_values
#audit axioms Rumoca.FMI3.StepEntry.call_frame
#audit axioms Rumoca.FMI3.StepEntry.final_values
#audit axioms Rumoca.FMI3.StepEntry.input_condition_all
#audit axioms Rumoca.FMI3.StepEntry.prefix_run

#audit axioms Rumoca.FMI3.ErrorContext.error_cast
#audit axioms Rumoca.FMI3.ErrorContext.instance_binding
#audit axioms Rumoca.FMI3.ErrorContext.logging_arguments
#audit axioms Rumoca.FMI3.ErrorContext.static
#audit axioms Rumoca.FMI3.ErrorContext.withRounding
#audit axioms Rumoca.FMI3.StaticErrors.statement_all_behaviors
#audit axioms Rumoca.FMI3.StaticErrors.statement_suppressed_behaviors
#audit axioms Rumoca.FMI3.StepErrors.lifecycle_logged
#audit axioms Rumoca.FMI3.StepErrors.lifecycle_prefix
#audit axioms Rumoca.FMI3.StepErrors.lifecycle_suppressed
#audit axioms Rumoca.FMI3.StepErrors.types

#audit axioms Rumoca.FMI3.StaticErrors.prefix_all_behaviors
#audit axioms Rumoca.FMI3.StaticErrors.prefix_suppressed_behaviors
#audit axioms Rumoca.FMI3.StepArguments.outputs_prefix
#audit axioms Rumoca.FMI3.StepArguments.Storage.instance_frame
#audit axioms Rumoca.FMI3.StepArguments.Storage.load_field
#audit axioms Rumoca.FMI3.StepArguments.input_prefix
#audit axioms Rumoca.FMI3.StepArguments.input_instance_frame
#audit axioms Rumoca.FMI3.StepArguments.output_cases
#audit axioms Rumoca.FMI3.StepArguments.outputs_suppressed
#audit axioms Rumoca.FMI3.StepArguments.outputs_logged
#audit axioms Rumoca.FMI3.StepArguments.input_suppressed
#audit axioms Rumoca.FMI3.StepArguments.input_logged

#audit axioms Rumoca.FMI3.StepArguments.ready_prefix
#audit axioms Rumoca.FMI3.StaticErrors.path_suppressed_behaviors
#audit axioms Rumoca.FMI3.StaticErrors.path_all_behaviors
#audit axioms Rumoca.FMI3.StepFailures.rounding_entry
#audit axioms Rumoca.FMI3.StepFailures.rounding_prefix
#audit axioms Rumoca.FMI3.StepFailures.stop_prefix
#audit axioms Rumoca.FMI3.StepFailures.rounding_suppressed
#audit axioms Rumoca.FMI3.StepFailures.rounding_logged
#audit axioms Rumoca.FMI3.StepFailures.stop_suppressed
#audit axioms Rumoca.FMI3.StepFailures.stop_logged

#audit axioms Rumoca.FMI3.StepDiscard.arguments_converted
#audit axioms Rumoca.FMI3.StepDiscard.resume_reaches
#audit axioms Rumoca.FMI3.StepDiscard.suppressed_reaches
#audit axioms Rumoca.FMI3.StepDiscard.dispatch_reaches
#audit axioms Rumoca.FMI3.StepDiscard.suppressed_behaviors
#audit axioms Rumoca.FMI3.StepDiscard.all_behaviors
#audit axioms Rumoca.FMI3.StepDiscard.public_prefix
#audit axioms Rumoca.FMI3.StepDiscard.call_suppressed
#audit axioms Rumoca.FMI3.StepDiscard.call_logged

#audit axioms Rumoca.FMI3.StepCases.input_values
#audit axioms Rumoca.FMI3.StepCases.complete
#audit axioms Rumoca.FMI3.StepCases.unique
#audit axioms Rumoca.FMI3.StepCases.partition
#audit axioms Rumoca.FMI3.StepCases.ready_values
#audit axioms Rumoca.FMI3.StepCases.accepted_values

#audit axioms Rumoca.FMI3.StaticErrors.prefix_path
#audit axioms Rumoca.FMI3.StepRejections.outputHeap_of_buffers
#audit axioms Rumoca.FMI3.StepRejections.public_path
#audit axioms Rumoca.FMI3.StepRejections.buffers_present
#audit axioms Rumoca.FMI3.StepRejections.before_frame
#audit axioms Rumoca.FMI3.StepRejections.before_load
#audit axioms Rumoca.FMI3.StepRejections.suppressed_call
#audit axioms Rumoca.FMI3.StepRejections.logged_call
#audit axioms Rumoca.FMI3.StepCalls.accepted_call
#audit axioms Rumoca.FMI3.StepCalls.accepted_correct
#audit axioms Rumoca.FMI3.StepCalls.null_correct
#audit axioms Rumoca.FMI3.StepCalls.suppressed_correct
#audit axioms Rumoca.FMI3.StepCalls.logged_correct
#audit axioms Rumoca.FMI3.StepCalls.outcome_cases
#audit axioms Rumoca.FMI3.StepCalls.message_collected
#audit axioms Rumoca.FMI3.StepCalls.prepared_correct
#audit axioms Rumoca.FMI3.StepCalls.rendered_contract

#audit axioms Rumoca.FMI3.CSHistory.accepted_case
#audit axioms Rumoca.FMI3.CSHistory.written_frame
#audit axioms Rumoca.FMI3.CSHistory.field_outside
#audit axioms Rumoca.FMI3.CSHistory.written_stored
#audit axioms Rumoca.FMI3.CSHistory.stored_call
#audit axioms Rumoca.FMI3.CSHistory.accepted_of_case
#audit axioms Rumoca.FMI3.CSHistory.step
#audit axioms Rumoca.FMI3.CSHistory.trace_frame
#audit axioms Rumoca.FMI3.CSHistory.ReferenceTrace.clock_monotone
#audit axioms Rumoca.FMI3.CSHistory.ReferenceTrace.duration_monotone
#audit axioms Rumoca.FMI3.InitializationEnvironment.enter_agrees
#audit axioms Rumoca.FMI3.InitializationEnvironment.exit_agrees
#audit axioms Rumoca.FMI3.InitializationEnvironment.calls
#audit axioms Rumoca.FMI3.CSHistory.initialized_stored
#audit axioms Rumoca.FMI3.TerminationEnvironment.body_agrees
#audit axioms Rumoca.FMI3.TerminationEnvironment.quiet_correct
#audit axioms Rumoca.FMI3.TerminationEnvironment.release_correct
#audit axioms Rumoca.FMI3.CSHistory.Stored.atomic_outside
#audit axioms Rumoca.FMI3.CSHistory.trace_atomic_frame
#audit axioms Rumoca.FMI3.CSHistory.release_history

#audit axioms Rumoca.FMI3.FactoryEnvironment.types
#audit axioms Rumoca.FMI3.FactoryEnvironment.scope
#audit axioms Rumoca.FMI3.FactoryEnvironment.admission
#audit axioms Rumoca.FMI3.FactoryEnvironment.create_owned
#audit axioms Rumoca.FMI3.StepArguments.Storage.storage_preserved
#audit axioms Rumoca.FMI3.StepArguments.Storage.at_index
#audit axioms Rumoca.FMI3.InstanceInitialization.Initialized.state_cell
#audit axioms Rumoca.FMI3.CSHistory.initialize_release

#audit axioms Rumoca.FMI3.ResetEnvironment.body_agrees
#audit axioms Rumoca.FMI3.ResetEnvironment.call_behaviors
#audit axioms Rumoca.FMI3.ResetEnvironment.null_behaviors
#audit axioms Rumoca.FMI3.ResetEnvironment.execution_correct
#audit axioms Rumoca.FMI3.StepRejections.after_frame
#audit axioms Rumoca.FMI3.StepRejections.after_kind
#audit axioms Rumoca.FMI3.StepRejections.after_mode
#audit axioms Rumoca.FMI3.StepRejections.after_reset_storage
#audit axioms Rumoca.FMI3.StepRejections.reset_after
#audit axioms Rumoca.FMI3.Reset.Storage.record_preserved
#audit axioms Rumoca.FMI3.StepRejections.after_atomic
#audit axioms Rumoca.FMI3.StepRejections.restarted_owners
#audit axioms Rumoca.FMI3.StepRejections.restarted_metadata

#audit axioms Rumoca.FMI3.CSRun.Stored.step_mode
#audit axioms Rumoca.FMI3.CSRun.Stored.advance
#audit axioms Rumoca.FMI3.CSRun.Stored.rejection_reads
#audit axioms Rumoca.FMI3.CSRun.rejection_buffers
#audit axioms Rumoca.FMI3.CSRun.Stored.reject
#audit axioms Rumoca.FMI3.CSRun.restart_storage
#audit axioms Rumoca.FMI3.CSRun.restart_buffers
#audit axioms Rumoca.FMI3.CSRun.Stored.restart
#audit axioms Rumoca.FMI3.CSRun.Stored.framed
#audit axioms Rumoca.FMI3.CSRun.change_step_total
#audit axioms Rumoca.FMI3.CSRun.Retains.trans
#audit axioms Rumoca.FMI3.CSRun.Retains.suppressed
#audit axioms Rumoca.FMI3.CSRun.advance_retains
#audit axioms Rumoca.FMI3.CSRun.reject_retains
#audit axioms Rumoca.FMI3.CSRun.restart_retains
#audit axioms Rumoca.FMI3.CSRun.Executed.readonly
#audit axioms Rumoca.FMI3.CSRun.restart_atomic
#audit axioms Rumoca.FMI3.CSRun.advance_atomic
#audit axioms Rumoca.FMI3.CSRun.Stored.initialized
#audit axioms Rumoca.FMI3.CSRun.change_correct
#audit axioms Rumoca.FMI3.CSRun.trace_correct

#audit axioms Rumoca.FMI3.CSRun.query_rehandle
#audit axioms Rumoca.FMI3.CSRun.Change.rehandle
#audit axioms Rumoca.FMI3.CSRun.ReferenceTrace.rehandle
#audit axioms Rumoca.FMI3.CSRun.Change.can_finish
#audit axioms Rumoca.FMI3.CSRun.ReferenceTrace.can_finish
#audit axioms Rumoca.FMI3.CSRun.Stored.mode_cell
#audit axioms Rumoca.FMI3.CSRun.finish_correct
#audit axioms Rumoca.FMI3.CSRun.Outside.field
#audit axioms Rumoca.FMI3.CSRun.Outside.cs
#audit axioms Rumoca.FMI3.CSRun.rejection_frame
#audit axioms Rumoca.FMI3.CSRun.initialize_frame
#audit axioms Rumoca.FMI3.CSRun.initialize_retains
#audit axioms Rumoca.FMI3.CSRun.Executed.heap_unique
#audit axioms Rumoca.FMI3.CSRun.executed_frame
#audit axioms Rumoca.FMI3.CSRun.trace_framed

#audit axioms Rumoca.FMI3.CSRun.Retains.logger
#audit axioms Rumoca.FMI3.CSRun.ProtectedFrame.run
#audit axioms Rumoca.FMI3.CSRun.ProtectedFrame.retains
#audit axioms Rumoca.FMI3.CSRun.ProtectedFrame.owners
#audit axioms Rumoca.FMI3.CSRun.ActionContract.step_behaviors
#audit axioms Rumoca.FMI3.CSRun.change_logged_correct
#audit axioms Rumoca.FMI3.CSRun.logged_trace_correct
#audit axioms Rumoca.FMI3.CSRun.ActionContract.returned
#audit axioms Rumoca.FMI3.CSRun.ActionContract.restart_returned
#audit axioms Rumoca.FMI3.CSRun.ActionContract.realizes
#audit axioms Rumoca.FMI3.CSRun.ActionContract.performed_iff
#audit axioms Rumoca.FMI3.CSRun.ActionContract.faulted_iff
#audit axioms Rumoca.FMI3.CSRun.ActionContract.progress
#audit axioms Rumoca.FMI3.CSRun.ActionContract.faulted_step
#audit axioms Rumoca.FMI3.CSRun.LoggedTrace.progress
#audit axioms Rumoca.FMI3.CSRun.LoggedTrace.completed

#audit axioms Rumoca.FMI3.CSRun.ActionContract.performed_status
#audit axioms Rumoca.FMI3.CSRun.LoggedTrace.statuses_eq

#audit axioms Rumoca.FMI3.StateEnvironment.body_agrees
#audit axioms Rumoca.FMI3.StateEnvironment.quiet_correct
#audit axioms Rumoca.FMI3.StateEnvironment.suppressed_correct
#audit axioms Rumoca.FMI3.StateEnvironment.logged_correct
#audit axioms Rumoca.FMI3.StateEnvironment.prepared_correct

#audit axioms Rumoca.FMI3.ModelRhsRuntime.parameters_bound
#audit axioms Rumoca.FMI3.ModelRhsRuntime.reaches
#audit axioms Rumoca.FMI3.ModelRhsRuntime.behaviors
#audit axioms Rumoca.FMI3.DerivativeEnvironment.body_agrees
#audit axioms Rumoca.FMI3.DerivativeEnvironment.get_reaches
#audit axioms Rumoca.FMI3.DerivativeEnvironment.quiet_correct
#audit axioms Rumoca.FMI3.DerivativeEnvironment.suppressed_correct
#audit axioms Rumoca.FMI3.DerivativeEnvironment.logged_correct
#audit axioms Rumoca.FMI3.DerivativeEnvironment.prepared_correct

#audit axioms Rumoca.FMI3.MEControlEnvironment.null_call
#audit axioms Rumoca.FMI3.MEControlEnvironment.EntryControl.body_agrees
#audit axioms Rumoca.FMI3.MEControlEnvironment.EntryControl.call_behaviors
#audit axioms Rumoca.FMI3.MEControlEnvironment.EntryControl.null_behaviors
#audit axioms Rumoca.FMI3.MEControlEnvironment.EntryControl.quiet_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.EntryControl.suppressed_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.EntryControl.logged_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.CompletedControl.body_agrees
#audit axioms Rumoca.FMI3.MEControlEnvironment.CompletedControl.call_behaviors
#audit axioms Rumoca.FMI3.MEControlEnvironment.CompletedControl.null_behaviors
#audit axioms Rumoca.FMI3.MEControlEnvironment.CompletedControl.quiet_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.CompletedControl.suppressed_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.CompletedControl.logged_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.DiscreteControl.body_agrees
#audit axioms Rumoca.FMI3.MEControlEnvironment.DiscreteControl.call_behaviors
#audit axioms Rumoca.FMI3.MEControlEnvironment.DiscreteControl.null_behaviors
#audit axioms Rumoca.FMI3.MEControlEnvironment.DiscreteControl.quiet_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.DiscreteControl.suppressed_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.DiscreteControl.logged_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.TimeControl.suppressed_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.TimeControl.logged_correct

#audit axioms Rumoca.FMI3.MEControlEnvironment.EntryControl.prepared_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.CompletedControl.prepared_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.DiscreteControl.prepared_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.TimeControl.prepared_correct
#audit axioms Rumoca.FMI3.MEEnvironment.PreparedContract.quiet
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.field_ne_buffer
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.state_ne_buffer
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.changed
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.write_buffer
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.prepare_buffer
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.write_state
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.control_frame
#audit axioms Rumoca.FMI3.MENumericalHistory.Action.prepare_correct
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.mode_loaded
#audit axioms Rumoca.FMI3.MENumericalHistory.Action.frame
#audit axioms Rumoca.FMI3.MENumericalHistory.step
#audit axioms Rumoca.FMI3.MENumericalHistory.Action.Prepares.unique
#audit axioms Rumoca.FMI3.MENumericalHistory.Action.Observes.unique
#audit axioms Rumoca.FMI3.MENumericalHistory.trace
#audit axioms Rumoca.FMI3.MENumericalHistory.Calls.executes
#audit axioms Rumoca.FMI3.MENumericalHistory.Calls.determines

#audit axioms Rumoca.FMI3.MENumericalHistory.action_atomic
#audit axioms Rumoca.FMI3.MENumericalHistory.trace_atomic
#audit axioms Rumoca.FMI3.MENumericalHistory.Action.next_live
#audit axioms Rumoca.FMI3.MENumericalHistory.ReferenceTrace.live
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.slot_outside
#audit axioms Rumoca.FMI3.MENumericalHistory.CallerStorage.storage_preserved
#audit axioms Rumoca.FMI3.MENumericalHistory.CallerStorage.at_index
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.callers
#audit axioms Rumoca.FMI3.MENumericalHistory.initialized_stored
#audit axioms Rumoca.FMI3.MENumericalHistory.initialize_release

#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.reset_storage
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.stop_outside
#audit axioms Rumoca.FMI3.MENumericalHistory.step_reset_storage
#audit axioms Rumoca.FMI3.MENumericalHistory.CallerStorage.reset
#audit axioms Rumoca.FMI3.MENumericalHistory.reset_state_cell
#audit axioms Rumoca.FMI3.MENumericalHistory.initialized_reset_storage
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.restart
#audit axioms Rumoca.FMI3.MENumericalHistory.restart_atomic
#audit axioms Rumoca.FMI3.MENumericalRun.Calls.executes
#audit axioms Rumoca.FMI3.MENumericalRun.Calls.determines
#audit axioms Rumoca.FMI3.MENumericalRun.restart_frame
#audit axioms Rumoca.FMI3.MENumericalRun.trace
#audit axioms Rumoca.FMI3.MENumericalRun.ReferenceTrace.live
#audit axioms Rumoca.FMI3.MENumericalRun.initialize_release

#audit axioms Rumoca.FMI3.MEFailure.Request.prepared
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.failed
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.failed_reset
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.failed_atomic
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.framed
#audit axioms Rumoca.FMI3.MENumericalHistory.Frame.reset_storage
#audit axioms Rumoca.FMI3.MEFailure.ProtectedFrame.numerical
#audit axioms Rumoca.FMI3.MEFailure.ProtectedFrame.owners
#audit axioms Rumoca.FMI3.MEFailure.Respects.returned
#audit axioms Rumoca.FMI3.MEFailure.Recovery.correct
#audit axioms Rumoca.FMI3.MEFailure.Recovery.determines
#audit axioms Rumoca.FMI3.MEFailure.Recovery.owners

#audit axioms Rumoca.FMI3.MEFailure.Prepares.unique
#audit axioms Rumoca.FMI3.MEFailure.prepare_frame
#audit axioms Rumoca.FMI3.MEFailure.prepare_correct
#audit axioms Rumoca.FMI3.MEFailure.Request.Selected.condition
#audit axioms Rumoca.FMI3.MEMixedRun.Configuration.Stored.framed
#audit axioms Rumoca.FMI3.MEMixedRun.configuration_outside
#audit axioms Rumoca.FMI3.MEMixedRun.ActionContract.realizes
#audit axioms Rumoca.FMI3.MEMixedRun.ActionContract.returned
#audit axioms Rumoca.FMI3.MEMixedRun.Trace.completed
#audit axioms Rumoca.FMI3.MEMixedRun.run_correct
#audit axioms Rumoca.FMI3.MEMixedRun.action_correct
#audit axioms Rumoca.FMI3.MEMixedRun.trace_correct

#audit axioms Rumoca.FMI3.LifecycleRelease.finish_correct
#audit axioms Rumoca.FMI3.MEMixedRun.Action.can_finish
#audit axioms Rumoca.FMI3.MEMixedRun.ReferenceTrace.can_finish
#audit axioms Rumoca.FMI3.MEMixedRun.Configuration.created
#audit axioms Rumoca.FMI3.MEMixedRun.Configuration.initialized
#audit axioms Rumoca.FMI3.MEMixedRun.Trace.slot

#audit axioms Rumoca.FMI3.Float64SetEnvironment.body_agrees
#audit axioms Rumoca.FMI3.Float64SetEnvironment.reaches
#audit axioms Rumoca.FMI3.Float64SetEnvironment.quiet_correct
#audit axioms Rumoca.FMI3.Float64SetEnvironment.failure_site
#audit axioms Rumoca.FMI3.Float64SetEnvironment.suppressed_correct
#audit axioms Rumoca.FMI3.Float64SetEnvironment.logged_correct
#audit axioms Rumoca.FMI3.Float64SetEnvironment.prepared_correct

#audit axioms Rumoca.FMI3.Float64Environment.body_agrees
#audit axioms Rumoca.FMI3.Float64Environment.helper_agrees
#audit axioms Rumoca.FMI3.Float64Environment.reaches
#audit axioms Rumoca.FMI3.Float64Environment.quiet_correct
#audit axioms Rumoca.FMI3.Float64Environment.failure_site
#audit axioms Rumoca.FMI3.Float64Environment.suppressed_correct
#audit axioms Rumoca.FMI3.Float64Environment.logged_correct
#audit axioms Rumoca.FMI3.Float64Environment.prepared_correct

#audit axioms Rumoca.FMI3.InitializationEnvironment.quiet_correct

#audit axioms Rumoca.FMI3.Float64Buffers.Stored.preserved
#audit axioms Rumoca.FMI3.Float64Buffers.different_blocks
#audit axioms Rumoca.FMI3.Float64Buffers.reference_converts
#audit axioms Rumoca.FMI3.Float64Buffers.references_run
#audit axioms Rumoca.FMI3.Float64Buffers.references_read
#audit axioms Rumoca.FMI3.Float64Buffers.references_frame
#audit axioms Rumoca.FMI3.Float64Buffers.references_preserve
#audit axioms Rumoca.FMI3.Float64Buffers.finite_written
#audit axioms Rumoca.FMI3.Float64Buffers.values_run
#audit axioms Rumoca.FMI3.Float64Buffers.values_preserve
#audit axioms Rumoca.FMI3.Float64Access.Instance.mode_loaded
#audit axioms Rumoca.FMI3.Float64Access.Instance.represented
#audit axioms Rumoca.FMI3.Float64Access.instance_outside
#audit axioms Rumoca.FMI3.Float64Access.Instance.changed
#audit axioms Rumoca.FMI3.Float64Access.Request.prepare_frame
#audit axioms Rumoca.FMI3.Float64Access.Request.prepare_correct
#audit axioms Rumoca.FMI3.Float64Access.Request.prepared_instance
#audit axioms Rumoca.FMI3.Float64Access.Request.prepared_references
#audit axioms Rumoca.FMI3.Float64Access.Request.volume
#audit axioms Rumoca.FMI3.Float64Access.Request.after_frame
#audit axioms Rumoca.FMI3.Float64Access.assigned_final
#audit axioms Rumoca.FMI3.Float64Access.assigned_correct
#audit axioms Rumoca.FMI3.Float64Access.step
#audit axioms Rumoca.FMI3.Float64Access.Request.readback_correct
#audit axioms Rumoca.FMI3.Float64Access.trace
#audit axioms Rumoca.FMI3.Float64Access.Calls.executes
#audit axioms Rumoca.FMI3.Float64Access.Calls.determines
#audit axioms Rumoca.FMI3.Float64Access.Calls.execution_iff
#audit axioms Rumoca.FMI3.InitializationAccess.start_allowed
#audit axioms Rumoca.FMI3.InitializationAccess.entry_storage
#audit axioms Rumoca.FMI3.InitializationAccess.entered_instance
#audit axioms Rumoca.FMI3.InitializationAccess.entered_buffers
#audit axioms Rumoca.FMI3.InitializationAccess.exited_instance
#audit axioms Rumoca.FMI3.InitializationAccess.exited_buffers
#audit axioms Rumoca.FMI3.InitializationAccess.initialization_history
#audit axioms Rumoca.FMI3.InitializationAccess.Certificate.executes
#audit axioms Rumoca.FMI3.InitializationAccess.Certificate.determines
#audit axioms Rumoca.FMI3.InitializationAccess.Certificate.execution_iff

#audit axioms Rumoca.FMI3.InitializationStorage.entered
#audit axioms Rumoca.FMI3.InitializationStorage.exited
#audit axioms Rumoca.FMI3.Float64Access.Request.host_atomic
#audit axioms Rumoca.FMI3.Float64Access.assigned_atomic
#audit axioms Rumoca.FMI3.Float64Access.Request.after_atomic
#audit axioms Rumoca.FMI3.InstanceInitialization.Initialized.access_instance
#audit axioms Rumoca.FMI3.Float64Buffers.Layout.Separate.at_index
#audit axioms Rumoca.FMI3.InitializationAccess.Certificate.owners
#audit axioms Rumoca.FMI3.InitializationAccess.Certificate.metadata
#audit axioms Rumoca.FMI3.InitializationAccess.Certificate.cs_storage
#audit axioms Rumoca.FMI3.InitializationAccess.Certificate.release

#audit axioms Rumoca.FMI3.CSRunEnvironment.PreparedContract.execution
#audit axioms Rumoca.FMI3.Reset.Storage.preserved
#audit axioms Rumoca.FMI3.InitializationAccess.Certificate.retains
#audit axioms Rumoca.FMI3.InitializationAccess.Certificate.cs_run_storage
#audit axioms Rumoca.FMI3.CSRun.Executed.performed
#audit axioms Rumoca.FMI3.CSRun.RecordedAction.performed
#audit axioms Rumoca.FMI3.CSRun.Performed.records
#audit axioms Rumoca.FMI3.CSRun.Recorded.completed
#audit axioms Rumoca.FMI3.CSRun.Completed.records
#audit axioms Rumoca.FMI3.CSRun.recorded_iff
#audit axioms Rumoca.FMI3.CSRun.RecordedAction.length
#audit axioms Rumoca.FMI3.CSRun.Recorded.length
#audit axioms Rumoca.FMI3.CSRun.SemanticAction.change
#audit axioms Rumoca.FMI3.CSRun.SemanticTrace.reference
#audit axioms Rumoca.FMI3.CSRun.Executed.recorded_correct
#audit axioms Rumoca.FMI3.CSRun.ActionContract.recorded_correct
#audit axioms Rumoca.FMI3.CSRun.Calls.executes
#audit axioms Rumoca.FMI3.CSRun.Calls.determines

#audit axioms Rumoca.FMI3.LifecycleEnvironment.PreparedContract.execution
#audit axioms Rumoca.FMI3.InitializationAccess.Certificate.field
#audit axioms Rumoca.FMI3.InitializationAccess.Certificate.me_storage
#audit axioms Rumoca.FMI3.InitializationAccess.Certificate.configuration

#audit axioms Rumoca.FMI3.Float64Buffers.raw_values_run
#audit axioms Rumoca.FMI3.Float64Buffers.raw_values_read
#audit axioms Rumoca.FMI3.Float64Buffers.raw_values_frame
#audit axioms Rumoca.FMI3.Float64Buffers.raw_values_preserve
#audit axioms Rumoca.FMI3.Float64Rejection.Request.prepared
#audit axioms Rumoca.FMI3.Float64Rejection.input_run
#audit axioms Rumoca.FMI3.Float64Rejection.input_read
#audit axioms Rumoca.FMI3.Float64Rejection.Request.prepare_frame
#audit axioms Rumoca.FMI3.Float64Rejection.Request.prepare_correct
#audit axioms Rumoca.FMI3.Float64Rejection.Request.prepared_instance
#audit axioms Rumoca.FMI3.LifecycleBodies.write_store
#audit axioms Rumoca.FMI3.LifecycleBodies.write_storage
#audit axioms Rumoca.FMI3.Float64Access.Instance.failed
#audit axioms Rumoca.FMI3.Float64Access.Instance.record_preserved
#audit axioms Rumoca.FMI3.Float64Rejection.Frame.record
#audit axioms Rumoca.FMI3.Float64Rejection.Frame.owners
#audit axioms Rumoca.FMI3.Float64Rejection.Frame.writable
#audit axioms Rumoca.FMI3.Reset.preserves
#audit axioms Rumoca.FMI3.Float64Access.Instance.reset
#audit axioms Rumoca.FMI3.InitializationAccess.Recovery.correct
#audit axioms Rumoca.FMI3.InitializationAccess.Recovery.executes
#audit axioms Rumoca.FMI3.InitializationAccess.Recovery.determines
#audit axioms Rumoca.FMI3.InitializationAccess.Recovery.execution_iff
#audit axioms Rumoca.FMI3.Float64Rejection.Request.behaves_iff
#audit axioms Rumoca.FMI3.Float64Rejection.Request.returned
#audit axioms Rumoca.FMI3.Float64Rejection.Returned.buffers
#audit axioms Rumoca.FMI3.Float64Rejection.Returned.recover
#audit axioms Rumoca.FMI3.Float64Rejection.Request.execution

#audit axioms Rumoca.FMI3.InitializationProtocol.Setup.entered
#audit axioms Rumoca.FMI3.InitializationProtocol.Setup.framed
#audit axioms Rumoca.FMI3.InitializationProtocol.Phase.Configured.framed
#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.entry
#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.access
#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.entered
#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.exited
#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.reset_done
#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.rejected
#audit axioms Rumoca.FMI3.InitializationProtocol.CallerStorage.refl
#audit axioms Rumoca.FMI3.InitializationProtocol.CallerStorage.trans
#audit axioms Rumoca.FMI3.InitializationProtocol.CallerStorage.ordinary
#audit axioms Rumoca.FMI3.InitializationProtocol.CallerStorage.request
#audit axioms Rumoca.FMI3.InitializationProtocol.CallContract.quiet
#audit axioms Rumoca.FMI3.InitializationProtocol.Result.ordinary
#audit axioms Rumoca.FMI3.InitializationProtocol.access_call
#audit axioms Rumoca.FMI3.InitializationProtocol.enter_call
#audit axioms Rumoca.FMI3.InitializationProtocol.exit_call
#audit axioms Rumoca.FMI3.InitializationProtocol.reset_call
#audit axioms Rumoca.FMI3.InitializationProtocol.LogPolicy.framed
#audit axioms Rumoca.FMI3.InitializationProtocol.Result.rejection
#audit axioms Rumoca.FMI3.InitializationProtocol.rejection_call
#audit axioms Rumoca.FMI3.InitializationProtocol.count_get_call
#audit axioms Rumoca.FMI3.InitializationProtocol.Result.count_rejected
#audit axioms Rumoca.FMI3.InitializationProtocol.count_rejection_call
#audit axioms Rumoca.FMI3.InitializationProtocol.Invariant.initial
#audit axioms Rumoca.FMI3.InitializationProtocol.Invariant.advance
#audit axioms Rumoca.FMI3.InitializationProtocol.execution_contract
#audit axioms Rumoca.FMI3.InitializationProtocol.Checkpoints.stored
#audit axioms Rumoca.FMI3.InitializationProtocol.Completed.correct
#audit axioms Rumoca.FMI3.InitializationProtocol.progress
#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.created
#audit axioms Rumoca.FMI3.InitializationProtocol.Phase.can_finish
#audit axioms Rumoca.FMI3.InitializationProtocol.Completed.release

#audit axioms Rumoca.FMI3.Float64Rejection.Returned.writable
#audit axioms Rumoca.FMI3.InitializationProtocol.LogPolicy.created
#audit axioms Rumoca.FMI3.InitializationProtocol.Invariant.created
#audit axioms Rumoca.FMI3.InitializationProtocol.CallerStorage.me_outputs
#audit axioms Rumoca.FMI3.InitializationProtocol.CallerStorage.cs_outputs
#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.me_ready
#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.cs_ready
#audit axioms Rumoca.FMI3.InitializationProtocol.Invariant.me_ready
#audit axioms Rumoca.FMI3.InitializationProtocol.Invariant.cs_ready
#audit axioms Rumoca.FMI3.InitializationProtocol.MEOutputsGuarded.protects
#audit axioms Rumoca.FMI3.InitializationProtocol.CSOutputsGuarded.protects
#audit axioms Rumoca.FMI3.InitializationProtocol.Retains.me_configuration
#audit axioms Rumoca.FMI3.InitializationProtocol.Retains.cs

#audit axioms Rumoca.FMI3.InitializationStorage.restarted
#audit axioms Rumoca.FMI3.HistoryProofs.write_storage
#audit axioms Rumoca.FMI3.HistoryProofs.raise_storage
#audit axioms Rumoca.FMI3.HistoryProofs.event_storage
#audit axioms Rumoca.FMI3.HistoryProofs.completed_storage
#audit axioms Rumoca.FMI3.MEHistory.action_storage
#audit axioms Rumoca.FMI3.MENumericalHistory.action_storage
#audit axioms Rumoca.FMI3.MENumericalHistory.restart_storage
#audit axioms Rumoca.FMI3.MEFailure.Prepares.storage
#audit axioms Rumoca.FMI3.MEMixedRun.Trace.storage
#audit axioms Rumoca.FMI3.StepEntry.output_storage
#audit axioms Rumoca.FMI3.StepAdvance.written_storage
#audit axioms Rumoca.FMI3.CSRun.advance_storage
#audit axioms Rumoca.FMI3.StepRejections.after_storage
#audit axioms Rumoca.FMI3.CSRun.LoggedTrace.storage
#audit axioms Rumoca.FMI3.CSRun.Calls.storage
#audit axioms Rumoca.FMI3.CSRun.Calls.atomic
#audit axioms Rumoca.FMI3.CSRun.Calls.retains
#audit axioms Rumoca.FMI3.CSRun.Calls.readonly
#audit axioms Rumoca.FMI3.CSRun.Calls.stored
#audit axioms Rumoca.FMI3.InitializationProtocol.Invariant.persistent
#audit axioms Rumoca.FMI3.InitializationProtocol.LogPolicy.cs
#audit axioms Rumoca.FMI3.InitializationProtocol.LogPolicy.me
#audit axioms Rumoca.FMI3.CSMixedRun.execution
#audit axioms Rumoca.FMI3.CSProtocol.Plan.Outside.not_record
#audit axioms Rumoca.FMI3.CSRun.Recorded.stopped
#audit axioms Rumoca.FMI3.CSRun.Interrupted.stopped
#audit axioms Rumoca.FMI3.CSRun.Stopped.interrupted
#audit axioms Rumoca.FMI3.CSRun.interrupted_iff
#audit axioms Rumoca.FMI3.CSRun.ReferenceTrace.split
#audit axioms Rumoca.FMI3.InitializationProtocol.Completed.stopped
#audit axioms Rumoca.FMI3.InitializationProtocol.Interrupted.stopped
#audit axioms Rumoca.FMI3.InitializationProtocol.Stopped.interrupted
#audit axioms Rumoca.FMI3.InitializationProtocol.interrupted_iff
#audit axioms Rumoca.FMI3.InitializationProtocol.ReferenceTrace.split
#audit axioms Rumoca.FMI3.CSProtocol.Interrupted.stopped
#audit axioms Rumoca.FMI3.CSProtocol.Stopped.interrupted
#audit axioms Rumoca.FMI3.CSProtocol.interrupted_iff
#audit axioms Rumoca.FMI3.InitializationProtocol.LogPolicy.fields
#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.reset_from
#audit axioms Rumoca.FMI3.InitializationProtocol.reset_invariant

#audit axioms Rumoca.FMI3.MENumericalRun.Calls.not_faulted
#audit axioms Rumoca.FMI3.MEMixedRun.ActionContract.performed_iff
#audit axioms Rumoca.FMI3.MEMixedRun.ActionContract.faulted_iff
#audit axioms Rumoca.FMI3.MEMixedRun.ActionContract.faulted_rejection
#audit axioms Rumoca.FMI3.MEMixedRun.ActionContract.progress
#audit axioms Rumoca.FMI3.MEMixedRun.Trace.progress
#audit axioms Rumoca.FMI3.MEMixedRun.Completed.stopped
#audit axioms Rumoca.FMI3.MEMixedRun.Interrupted.stopped
#audit axioms Rumoca.FMI3.MEMixedRun.Stopped.interrupted
#audit axioms Rumoca.FMI3.MEMixedRun.interrupted_iff
#audit axioms Rumoca.FMI3.MEMixedRun.ReferenceTrace.split
#audit axioms Rumoca.FMI3.MEMixedRun.Trace.take
#audit axioms Rumoca.FMI3.MEMixedRun.Trace.after_prefix
#audit axioms Rumoca.FMI3.MEMixedRun.retained_field_outside
#audit axioms Rumoca.FMI3.InitializationProtocol.me_execution

#audit axioms Rumoca.FMI3.MEProtocol.Cycle.Admitted.can_finish
#audit axioms Rumoca.FMI3.MEProtocol.Plan.Outside.not_record
#audit axioms Rumoca.FMI3.MEProtocol.Interrupted.stopped
#audit axioms Rumoca.FMI3.MEProtocol.Stopped.interrupted
#audit axioms Rumoca.FMI3.MEProtocol.interrupted_iff

-- Count calls in mixed ME histories retain original caller storage and raw observations.
#audit axioms Rumoca.FMI3.MECountCalls.written_frame
#audit axioms Rumoca.FMI3.MECountCalls.written_memory
#audit axioms Rumoca.FMI3.MECountCalls.configuration_frame
#audit axioms Rumoca.FMI3.MECountCalls.Memory.success
#audit axioms Rumoca.FMI3.MECountCalls.Memory.failure
#audit axioms Rumoca.FMI3.MECountCalls.Contract.quiet
#audit axioms Rumoca.FMI3.MECountCalls.execution
#audit axioms Rumoca.FMI3.MEMixedRun.Configuration.StoragePolicy.mono
#audit axioms Rumoca.FMI3.MEMixedRun.Action.Prepared.preserved

#audit axioms Rumoca.FMI3.Nominals.body_eq
#audit axioms Rumoca.FMI3.Nominals.failure_prefix
#audit axioms Rumoca.FMI3.NominalEnvironment.body_agrees
#audit axioms Rumoca.FMI3.NominalEnvironment.quiet_correct
#audit axioms Rumoca.FMI3.NominalEnvironment.quiet_returned
#audit axioms Rumoca.FMI3.NominalEnvironment.suppressed_correct
#audit axioms Rumoca.FMI3.NominalEnvironment.logged_correct
#audit axioms Rumoca.FMI3.NominalEnvironment.prepared_correct
#audit axioms Rumoca.FMI3.NominalAccess.Request.OutputStorage.preserved
#audit axioms Rumoca.FMI3.NominalAccess.Request.get_observed
#audit axioms Rumoca.FMI3.NominalAccess.request_coverage
#audit axioms Rumoca.FMI3.MEHistory.Stored.record_storage_preserved
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.record_storage_preserved
#audit axioms Rumoca.FMI3.Nominals.written_store
#audit axioms Rumoca.FMI3.Nominals.written_memory
#audit axioms Rumoca.FMI3.Nominals.written_me_memory
#audit axioms Rumoca.FMI3.InitializationProtocol.nominal_get_call
#audit axioms Rumoca.FMI3.InitializationProtocol.Result.nominal_rejected
#audit axioms Rumoca.FMI3.InitializationProtocol.nominal_rejection_call
#audit axioms Rumoca.FMI3.MENominalCalls.separate_frame
#audit axioms Rumoca.FMI3.MENominalCalls.Memory.success
#audit axioms Rumoca.FMI3.MENominalCalls.Memory.failure
#audit axioms Rumoca.FMI3.MENominalCalls.Contract.quiet
#audit axioms Rumoca.FMI3.MENominalCalls.execution

#audit axioms Rumoca.FMI3.DebugLogging.iteration_closed
#audit axioms Rumoca.FMI3.DebugLogging.category_eval
#audit axioms Rumoca.FMI3.DebugLogging.null_category_step
#audit axioms Rumoca.FMI3.DebugLogging.difference_step
#audit axioms Rumoca.FMI3.DebugLogging.iteration_valid_equivalence
#audit axioms Rumoca.FMI3.DebugLogging.entry_eval
#audit axioms Rumoca.FMI3.DebugLogging.validation_prefix_equivalence
#audit axioms Rumoca.FMI3.DebugLogging.validation_valid_equivalence
#audit axioms Rumoca.FMI3.DebugLogging.suppressed_failure_contract
#audit axioms Rumoca.FMI3.DebugLogging.logged_failure_contract
#audit axioms Rumoca.FMI3.DebugLogging.iteration_invalid_behaviors
#audit axioms Rumoca.FMI3.DebugLogging.category_cases
#audit axioms Rumoca.FMI3.DebugLogging.validation_rejected_behaviors
#audit axioms Rumoca.FMI3.DebugLogging.written_store
#audit axioms Rumoca.FMI3.DebugLogging.written_frame
#audit axioms Rumoca.FMI3.DebugLogging.written_storage
#audit axioms Rumoca.FMI3.DebugLogging.missing_step
#audit axioms Rumoca.FMI3.DebugLogging.declarations_reaches
#audit axioms Rumoca.FMI3.DebugLogging.write_logging_step
#audit axioms Rumoca.FMI3.DebugLogging.finish_reaches
#audit axioms Rumoca.FMI3.DebugLogging.prepare_code
#audit axioms Rumoca.FMI3.DebugLogging.Entries.readable
#audit axioms Rumoca.FMI3.DebugLogging.code_success_behaviors
#audit axioms Rumoca.FMI3.DebugLogging.code_unknown_behaviors
#audit axioms Rumoca.FMI3.DebugLogging.code_missing_behaviors
#audit axioms Rumoca.FMI3.DebugLogging.code_behaviors
#audit axioms Rumoca.FMI3.DebugLogging.public_scope
#audit axioms Rumoca.FMI3.DebugLogging.function_closed
#audit axioms Rumoca.FMI3.DebugLogging.parameters_bound
#audit axioms Rumoca.FMI3.DebugLogging.logging_guard_run
#audit axioms Rumoca.FMI3.DebugLogging.entry_run
#audit axioms Rumoca.FMI3.DebugLogging.null_run
#audit axioms Rumoca.FMI3.DebugLogging.public_prefix
#audit axioms Rumoca.FMI3.DebugLogging.public_null_behaviors
#audit axioms Rumoca.FMI3.DebugLogging.call_behaviors
#audit axioms Rumoca.FMI3.DebugLogging.call_success_behaviors
#audit axioms Rumoca.FMI3.DebugLogging.written_flag
#audit axioms Rumoca.FMI3.DebugLogging.call_success_returned
#audit axioms Rumoca.FMI3.DebugLogging.described_category
#audit axioms Rumoca.FMI3.DebugLogging.artifact_category
#audit axioms Rumoca.FMI3.DebugLogging.legal_single_accepted
#audit axioms Rumoca.FMI3.DebugLogging.legal_empty_null
#audit axioms Rumoca.FMI3.DebugLogging.message_collected
#audit axioms Rumoca.FMI3.DebugLogging.runtime_types
#audit axioms Rumoca.FMI3.DebugLogging.runtime_library
#audit axioms Rumoca.FMI3.DebugLogging.prepared_definitions
#audit axioms Rumoca.FMI3.DebugLogging.prepared_literals
#audit axioms Rumoca.FMI3.DebugLogging.runtime_suppressed_correct
#audit axioms Rumoca.FMI3.DebugLogging.runtime_logged_correct
#audit axioms Rumoca.FMI3.DebugLogging.runtime_null_correct
#audit axioms Rumoca.FMI3.DebugLogging.prepared_correct
#audit axioms Rumoca.FMI3.DebugLogging.legal_behaviors
#audit axioms Rumoca.FMI3.DebugLogging.legal_returned
#audit axioms Rumoca.FMI3.DebugLogging.function_eq
#audit axioms Rumoca.FMI3.DebugLogging.rendered_contract

#audit axioms Rumoca.FMI3.InitializationProtocol.Stored.logging_framed
#audit axioms Rumoca.FMI3.InitializationProtocol.logging_legal_returned
#audit axioms Rumoca.FMI3.InitializationProtocol.logging_failure_returned
#audit axioms Rumoca.FMI3.DebugLogging.input_empty
#audit axioms Rumoca.FMI3.DebugLogging.Entries.framed
#audit axioms Rumoca.FMI3.InitializationProtocol.ReadBank.Frame.refl
#audit axioms Rumoca.FMI3.InitializationProtocol.ReadBank.Frame.trans
#audit axioms Rumoca.FMI3.InitializationProtocol.ReadBank.Stored.framed
#audit axioms Rumoca.FMI3.InitializationProtocol.Result.inputs_framed
#audit axioms Rumoca.FMI3.InitializationProtocol.logging_call
#audit axioms Rumoca.FMI3.InitializationProtocol.Retention.of_retains
#audit axioms Rumoca.FMI3.InitializationProtocol.Retention.to_retains
#audit axioms Rumoca.FMI3.InitializationProtocol.Retention.refl
#audit axioms Rumoca.FMI3.InitializationProtocol.Retention.trans
#audit axioms Rumoca.FMI3.InitializationProtocol.Retention.writable
#audit axioms Rumoca.FMI3.InitializationProtocol.Retention.configured
#audit axioms Rumoca.FMI3.InitializationProtocol.Retention.logging_written
#audit axioms Rumoca.FMI3.Logging.Capability.requires_mono
#audit axioms Rumoca.FMI3.Logging.Capability.requires_and
#audit axioms Rumoca.FMI3.Logging.Capability.Stored.framed
#audit axioms Rumoca.FMI3.Logging.Capability.Stored.logging_written
#audit axioms Rumoca.FMI3.Logging.Capability.Stored.mode_written
#audit axioms Rumoca.FMI3.Logging.Capability.Configured.logging_written
#audit axioms Rumoca.FMI3.Logging.Capability.Configured.framed
#audit axioms Rumoca.FMI3.Logging.Capability.cs_stored
#audit axioms Rumoca.FMI3.Logging.Capability.cs_bound
#audit axioms Rumoca.FMI3.Logging.Capability.cs_respects
#audit axioms Rumoca.FMI3.Logging.Capability.cs_storage
#audit axioms Rumoca.FMI3.Logging.Capability.cs_control
#audit axioms Rumoca.FMI3.Logging.Capability.request_contract
#audit axioms Rumoca.FMI3.Logging.Capability.legal_returned
#audit axioms Rumoca.FMI3.Logging.Capability.factory_policy
#audit axioms Rumoca.FMI3.Logging.Capability.created
#audit axioms Rumoca.FMI3.Logging.Capability.created_invariant
#audit axioms Rumoca.FMI3.Logging.Capability.prepared_request
#audit axioms Rumoca.FMI3.Logging.Capability.initialization_control
#audit axioms Rumoca.FMI3.Logging.Capability.me_control
#audit axioms Rumoca.FMI3.Logging.Capability.Configured.mode_written
#audit axioms Rumoca.FMI3.Logging.Capability.Failure.returned
#audit axioms Rumoca.FMI3.Logging.Capability.Failure.progress
#audit axioms Rumoca.FMI3.Logging.Capability.initialized
#audit axioms Rumoca.FMI3.Logging.Capability.Configured.reset
#audit axioms Rumoca.FMI3.Logging.Capability.Configured.initialization_retained
#audit axioms Rumoca.FMI3.Logging.Capability.me_stored
#audit axioms Rumoca.FMI3.Logging.Capability.me_valid
#audit axioms Rumoca.FMI3.Logging.Capability.me_storage
#audit axioms Rumoca.FMI3.Logging.Capability.initialization_policy
#audit axioms Rumoca.FMI3.DebugLogging.Request.logging_update
#audit axioms Rumoca.FMI3.DebugLogging.Request.legal_accepted
#audit axioms Rumoca.FMI3.DebugLogging.Request.legal_logging
#audit axioms Rumoca.FMI3.DebugLogging.Request.Inputs.framed
#audit axioms Rumoca.FMI3.InitializationProtocol.LogPolicy.current
#audit axioms Rumoca.FMI3.InitializationProtocol.LogPolicy.updated

#audit axioms Rumoca.FMI3.DebugLogging.Entries.load_ne_none
#audit axioms Rumoca.FMI3.DebugLogging.Request.Inputs.load_ne_none
#audit axioms Rumoca.FMI3.InitializationProtocol.ReadBank.Stored.not_flag
#audit axioms Rumoca.FMI3.InitializationProtocol.ReadBank.Stored.creation_frame
#audit axioms Rumoca.FMI3.InitializationProtocol.Retention.logging_value
#audit axioms Rumoca.FMI3.InitializationProtocol.Retention.me_created
#audit axioms Rumoca.FMI3.CSRun.Logger.FramePolicy.storage
#audit axioms Rumoca.FMI3.CSRun.LoggedTrace.frame

#audit axioms Rumoca.FMI3.MEMixedRun.Configuration.FramePolicy.storage
#audit axioms Rumoca.FMI3.MEMixedRun.Configuration.FramePolicy.mono
#audit axioms Rumoca.FMI3.MEMixedRun.Trace.callerFrame
#audit axioms Rumoca.FMI3.CSRun.Calls.frame

#audit axioms Rumoca.FMI3.CSLoggingCalls.Contract.quiet
#audit axioms Rumoca.FMI3.CSLoggingCalls.Memory.failure
#audit axioms Rumoca.FMI3.CSLoggingCalls.Memory.retention
#audit axioms Rumoca.FMI3.CSLoggingCalls.Memory.success
#audit axioms Rumoca.FMI3.CSLoggingCalls.execution
#audit axioms Rumoca.FMI3.CSRun.Stored.failed
#audit axioms Rumoca.FMI3.CSRun.Stored.logging_framed
#audit axioms Rumoca.FMI3.CSRun.logging_failure_returned
#audit axioms Rumoca.FMI3.CSRun.logging_legal_returned
#audit axioms Rumoca.FMI3.InitializationAccess.Certificate.retention
#audit axioms Rumoca.FMI3.Logging.Capability.Failure.cases
#audit axioms Rumoca.FMI3.Logging.Capability.Failure.memory
#audit axioms Rumoca.FMI3.Logging.Capability.Failure.storage
#audit axioms Rumoca.FMI3.Logging.Capability.cs_frame
#audit axioms Rumoca.FMI3.Logging.Capability.me_frame
#audit axioms Rumoca.FMI3.MELoggingCalls.Contract.quiet
#audit axioms Rumoca.FMI3.MELoggingCalls.Memory.failure
#audit axioms Rumoca.FMI3.MELoggingCalls.Memory.retention
#audit axioms Rumoca.FMI3.MELoggingCalls.Memory.success
#audit axioms Rumoca.FMI3.MELoggingCalls.execution
#audit axioms Rumoca.FMI3.MEMixedRun.Returned.of_frame
#audit axioms Rumoca.FMI3.MEMixedRun.loggingUpdate_cons_getD
#audit axioms Rumoca.FMI3.MENumericalHistory.Stored.logging_framed
#audit axioms Rumoca.FMI3.MENumericalHistory.logging_failure_returned
#audit axioms Rumoca.FMI3.MENumericalHistory.logging_legal_returned

#audit axioms Rumoca.FMI3.CSMixedRun.Action.Prepared.framed

#audit axioms Rumoca.FMI3.CSMixedRun.ActionContract.faulted_iff

#audit axioms Rumoca.FMI3.CSMixedRun.ActionContract.faulted_kind

#audit axioms Rumoca.FMI3.CSMixedRun.ActionContract.performed_iff

#audit axioms Rumoca.FMI3.CSMixedRun.ActionContract.progress

#audit axioms Rumoca.FMI3.CSMixedRun.ActionContract.realizes

#audit axioms Rumoca.FMI3.CSMixedRun.ActionContract.returned

#audit axioms Rumoca.FMI3.CSMixedRun.ActionContract.run_recorded

#audit axioms Rumoca.FMI3.CSMixedRun.Change.can_finish

#audit axioms Rumoca.FMI3.CSMixedRun.Change.rehandle

#audit axioms Rumoca.FMI3.CSMixedRun.Completed.records

#audit axioms Rumoca.FMI3.CSMixedRun.Interrupted.stopped

#audit axioms Rumoca.FMI3.CSMixedRun.Performed.records

#audit axioms Rumoca.FMI3.CSMixedRun.Recorded.completed

#audit axioms Rumoca.FMI3.CSMixedRun.Recorded.stopped

#audit axioms Rumoca.FMI3.CSMixedRun.RecordedAction.performed

#audit axioms Rumoca.FMI3.CSMixedRun.ReferenceTrace.can_finish

#audit axioms Rumoca.FMI3.CSMixedRun.ReferenceTrace.rehandle

#audit axioms Rumoca.FMI3.CSMixedRun.ReferenceTrace.split

#audit axioms Rumoca.FMI3.CSMixedRun.Returned.logged

#audit axioms Rumoca.FMI3.CSMixedRun.Returned.logging

#audit axioms Rumoca.FMI3.CSMixedRun.Returned.quiet

#audit axioms Rumoca.FMI3.CSMixedRun.Stopped.decompose

#audit axioms Rumoca.FMI3.CSMixedRun.Stopped.interrupted

#audit axioms Rumoca.FMI3.CSMixedRun.Trace.after_prefix

#audit axioms Rumoca.FMI3.CSMixedRun.Trace.callerFrame

#audit axioms Rumoca.FMI3.CSMixedRun.Trace.completed

#audit axioms Rumoca.FMI3.CSMixedRun.Trace.progress

#audit axioms Rumoca.FMI3.CSMixedRun.Trace.reference_of_completed

#audit axioms Rumoca.FMI3.CSMixedRun.Trace.released

#audit axioms Rumoca.FMI3.CSMixedRun.Trace.released_frame

#audit axioms Rumoca.FMI3.CSMixedRun.Trace.stopped_prefix

#audit axioms Rumoca.FMI3.CSMixedRun.Trace.storage

#audit axioms Rumoca.FMI3.CSMixedRun.action_correct

#audit axioms Rumoca.FMI3.CSMixedRun.configuration_cases

#audit axioms Rumoca.FMI3.CSMixedRun.interrupted_iff

#audit axioms Rumoca.FMI3.CSMixedRun.loggingUpdate_cons_getD

#audit axioms Rumoca.FMI3.CSMixedRun.recorded_iff

#audit axioms Rumoca.FMI3.CSMixedRun.trace_correct

#audit axioms Rumoca.FMI3.CSProtocol.Cycle.Admitted.can_finish

#audit axioms Rumoca.FMI3.EventIndicatorAccess.request_coverage
#audit axioms Rumoca.FMI3.EventIndicatorCalls.QuietContract.get_refines
#audit axioms Rumoca.FMI3.EventIndicatorCalls.accepted_run
#audit axioms Rumoca.FMI3.EventIndicatorCalls.allowed_iff
#audit axioms Rumoca.FMI3.EventIndicatorCalls.behaviors
#audit axioms Rumoca.FMI3.EventIndicatorCalls.body_eq
#audit axioms Rumoca.FMI3.EventIndicatorCalls.failure_message_collected
#audit axioms Rumoca.FMI3.EventIndicatorCalls.failure_prefix
#audit axioms Rumoca.FMI3.EventIndicatorCalls.failure_unique
#audit axioms Rumoca.FMI3.EventIndicatorCalls.invalid_run
#audit axioms Rumoca.FMI3.EventIndicatorCalls.null_behaviors
#audit axioms Rumoca.FMI3.EventIndicatorCalls.parameters_bound
#audit axioms Rumoca.FMI3.EventIndicatorCalls.query_cases
#audit axioms Rumoca.FMI3.EventIndicatorCalls.reaches
#audit axioms Rumoca.FMI3.EventIndicatorCalls.rendered_contract
#audit axioms Rumoca.FMI3.EventIndicatorEnvironment.body_agrees
#audit axioms Rumoca.FMI3.EventIndicatorEnvironment.logged_correct
#audit axioms Rumoca.FMI3.EventIndicatorEnvironment.prepared_correct
#audit axioms Rumoca.FMI3.EventIndicatorEnvironment.quiet_correct
#audit axioms Rumoca.FMI3.EventIndicatorEnvironment.suppressed_correct
#audit axioms Rumoca.FMI3.MEEventIndicatorCalls.Contract.quiet
#audit axioms Rumoca.FMI3.MEEventIndicatorCalls.Memory.failure
#audit axioms Rumoca.FMI3.MEEventIndicatorCalls.Memory.success
#audit axioms Rumoca.FMI3.MEEventIndicatorCalls.execution

#audit axioms Rumoca.FMI3.InitializationProtocol.event_indicators_get_call

#audit axioms Rumoca.FMI3.InitializationProtocol.Result.event_indicators_rejected

#audit axioms Rumoca.FMI3.InitializationProtocol.event_indicators_rejection_call

#audit axioms Rumoca.FMI3.DiscreteEvaluation.artifact_capability
#audit axioms Rumoca.FMI3.DiscreteEvaluation.body_agrees
#audit axioms Rumoca.FMI3.DiscreteEvaluation.body_agrees_static
#audit axioms Rumoca.FMI3.DiscreteEvaluation.described_capability
#audit axioms Rumoca.FMI3.DiscreteEvaluation.failure_prefix
#audit axioms Rumoca.FMI3.DiscreteEvaluation.logged_correct
#audit axioms Rumoca.FMI3.DiscreteEvaluation.message_collected
#audit axioms Rumoca.FMI3.DiscreteEvaluation.parameters_bound
#audit axioms Rumoca.FMI3.DiscreteEvaluation.prepared_correct
#audit axioms Rumoca.FMI3.DiscreteEvaluation.query_cases
#audit axioms Rumoca.FMI3.DiscreteEvaluation.quiet_agreed
#audit axioms Rumoca.FMI3.DiscreteEvaluation.quiet_correct
#audit axioms Rumoca.FMI3.DiscreteEvaluation.quiet_static_correct
#audit axioms Rumoca.FMI3.DiscreteEvaluation.rendered_contract
#audit axioms Rumoca.FMI3.DiscreteEvaluation.suppressed_correct
#audit axioms Rumoca.FMI3.GuardedCalls.unchanged_body
#audit axioms Rumoca.FMI3.MEHistory.evaluation_preserves_iteration
#audit axioms Rumoca.FMI3.MEHistory.initial_evaluation_still_requires_iteration

#audit axioms Rumoca.FMI3.DiscreteEvaluation.classify_correct
#audit axioms Rumoca.FMI3.DiscreteEvaluation.request_coverage
#audit axioms Rumoca.FMI3.InitializationProtocol.Result.evaluation_rejected
#audit axioms Rumoca.FMI3.InitializationProtocol.evaluation_call
#audit axioms Rumoca.FMI3.InitializationProtocol.evaluation_rejection_call

#audit axioms Rumoca.FMI3.AbsentVariables.Absent.no_declaration
#audit axioms Rumoca.FMI3.AbsentVariables.Absent.selection_empty
#audit axioms Rumoca.FMI3.AbsentVariables.QuietContract.selection_call
#audit axioms Rumoca.FMI3.AbsentVariables.artifact_absence
#audit axioms Rumoca.FMI3.AbsentVariables.body_agrees
#audit axioms Rumoca.FMI3.AbsentVariables.body_agrees_static
#audit axioms Rumoca.FMI3.AbsentVariables.body_eq
#audit axioms Rumoca.FMI3.AbsentVariables.described_absence
#audit axioms Rumoca.FMI3.AbsentVariables.empty_behaviors
#audit axioms Rumoca.FMI3.AbsentVariables.empty_body
#audit axioms Rumoca.FMI3.AbsentVariables.family_correct
#audit axioms Rumoca.FMI3.AbsentVariables.logged_correct
#audit axioms Rumoca.FMI3.AbsentVariables.message_collected
#audit axioms Rumoca.FMI3.AbsentVariables.nonempty_body
#audit axioms Rumoca.FMI3.AbsentVariables.nonempty_prefix
#audit axioms Rumoca.FMI3.AbsentVariables.null_behaviors
#audit axioms Rumoca.FMI3.AbsentVariables.parameters_bound
#audit axioms Rumoca.FMI3.AbsentVariables.prepared_correct
#audit axioms Rumoca.FMI3.AbsentVariables.quiet_agreed
#audit axioms Rumoca.FMI3.AbsentVariables.quiet_correct
#audit axioms Rumoca.FMI3.AbsentVariables.quiet_static_correct
#audit axioms Rumoca.FMI3.AbsentVariables.rendered_contract
#audit axioms Rumoca.FMI3.AbsentVariables.selected_cardinalities_zero
#audit axioms Rumoca.FMI3.AbsentVariables.signature_printable
#audit axioms Rumoca.FMI3.AbsentVariables.suppressed_correct
#audit axioms Rumoca.FMI3.AbsentVariables.value_type_printable

-- Raw absent-variable requests and complete initialization call composition.
#audit axioms Rumoca.FMI3.AbsentVariables.classify_correct
#audit axioms Rumoca.FMI3.AbsentVariables.classify_call
#audit axioms Rumoca.FMI3.AbsentVariables.request_coverage
#audit axioms Rumoca.FMI3.InitializationProtocol.absent_empty_call
#audit axioms Rumoca.FMI3.InitializationProtocol.Result.absent_rejected
#audit axioms Rumoca.FMI3.InitializationProtocol.absent_rejection_call

-- Existing unsupported public calls, their printers and actual-source contracts.
#audit axioms Rumoca.FMI3.CapabilityRejection.locals_instance
#audit axioms Rumoca.FMI3.CapabilityRejection.arguments_exist
#audit axioms Rumoca.FMI3.CapabilityRejection.locals_fresh
#audit axioms Rumoca.FMI3.CapabilityRejection.parameters_bound
#audit axioms Rumoca.FMI3.CapabilityRejection.nonnull_body
#audit axioms Rumoca.FMI3.CapabilityRejection.failure_prefix
#audit axioms Rumoca.FMI3.CapabilityRejection.null_body
#audit axioms Rumoca.FMI3.CapabilityRejection.code_agrees
#audit axioms Rumoca.FMI3.CapabilityRejection.null_call
#audit axioms Rumoca.FMI3.CapabilityRejection.suppressed_call
#audit axioms Rumoca.FMI3.CapabilityRejection.logged_call
#audit axioms Rumoca.FMI3.CapabilityRejection.failures_correct
#audit axioms Rumoca.FMI3.CapabilityRejection.message_collected
#audit axioms Rumoca.FMI3.CapabilityRejection.prepared_correct
#audit axioms Rumoca.FMI3.CapabilityRejection.rendered_contract
#audit axioms Rumoca.FMI3.ScheduledCreation.scope
#audit axioms Rumoca.FMI3.ScheduledCreation.body
#audit axioms Rumoca.FMI3.ScheduledCreation.arguments_converted
#audit axioms Rumoca.FMI3.ScheduledCreation.call_entry
#audit axioms Rumoca.FMI3.ScheduledCreation.quiet_call
#audit axioms Rumoca.FMI3.ScheduledCreation.logged_call
#audit axioms Rumoca.FMI3.ScheduledCreation.message_collected
#audit axioms Rumoca.FMI3.ScheduledCreation.prepared_correct
#audit axioms Rumoca.FMI3.ScheduledCreation.signature_printable
#audit axioms Rumoca.FMI3.ScheduledCreation.rendered_contract
#audit axioms Rumoca.FMI3.CapabilityMetadata.described
#audit axioms Rumoca.FMI3.CapabilityMetadata.no_clock_or_structural_parameter
#audit axioms Rumoca.FMI3.CapabilityMetadata.artifact
#audit axioms Rumoca.FMI3.CapabilityRejection.routing
#audit axioms Rumoca.FMI3.CapabilityRejection.profiles
#audit axioms Rumoca.FMI3.CapabilityRejection.signatures_printable
#audit axioms Rumoca.FMI3.CapabilityRejection.family_correct
#audit axioms Rumoca.FMI3.CapabilityRejection.all_correct

#audit axioms Rumoca.FMI3.SetterScope.nested_empty_reject
#audit axioms Rumoca.FMI3.SetterScope.hoisted_empty_reject
#audit axioms Rumoca.FMI3.Float64Set.empty_lifecycle_site
#audit axioms Rumoca.FMI3.AbsentVariables.failure_unique
#audit axioms Rumoca.FMI3.AbsentVariables.failure_prefix
#audit axioms Rumoca.FMI3.AbsentVariables.terminated_setter
#audit axioms Rumoca.FMI3.AbsentVariables.cs_step_empty
#audit axioms Rumoca.FMI3.PublicAPI.every_export

-- Tensor FMI 3 model description (package-checked product; no production emission).
#audit axioms Rumoca.FMI3.TensorMetadata.text_toString
#audit axioms Rumoca.FMI3.TensorMetadata.startEntries_length
#audit axioms Rumoca.FMI3.TensorMetadata.startValue_text
#audit axioms Rumoca.FMI3.TensorMetadata.valid
#audit axioms Rumoca.FMI3.TensorMetadata.document
#audit axioms Rumoca.FMI3.TensorMetadata.valueReferences_eq
#audit axioms Rumoca.FMI3.TensorMetadata.valueReferences_nodup
#audit axioms Rumoca.FMI3.TensorMetadata.dimStarts_dimensions
#audit axioms Rumoca.FMI3.TensorMetadata.stateVar_dim_product
#audit axioms Rumoca.FMI3.TensorMetadata.inputVar_dim_product
#audit axioms Rumoca.FMI3.TensorMetadata.derivativeVar_dim_product
#audit axioms Rumoca.FMI3.TensorMetadata.outputVar_dim_product
#audit axioms Rumoca.FMI3.TensorMetadata.derivative_references_state
#audit axioms Rumoca.FMI3.TensorMetadata.structure_references_declared
#audit axioms Rumoca.FMI3.TensorMetadata.structure_dependencies_declared
#audit axioms Rumoca.FMI3.TensorMetadata.modelIdentifiers_decode
#audit axioms Rumoca.FMI3.TensorMetadata.token_attribute

-- Tensor instance storage bound to the model right-hand side (package-checked
#audit axioms Rumoca.FMI3.TensorInstance.reads_state
#audit axioms Rumoca.FMI3.TensorInstance.reads_input
#audit axioms Rumoca.FMI3.TensorInstance.writable_derivative
#audit axioms Rumoca.FMI3.TensorInstance.fields_separate
#audit axioms Rumoca.FMI3.TensorInstance.instances_separate
#audit axioms Rumoca.FMI3.TensorInstance.store_other_instance
#audit axioms Rumoca.FMI3.TensorInstanceRhs.derivative_valid
#audit axioms Rumoca.FMI3.TensorInstanceRhs.derivativeBuffer_eq
#audit axioms Rumoca.FMI3.TensorInstanceRhs.parameter_bound
#audit axioms Rumoca.FMI3.TensorInstanceRhs.derivative_writes
#audit axioms Rumoca.FMI3.TensorInstanceRhs.buffer_outside
#audit axioms Rumoca.FMI3.TensorInstanceRhs.derivative_writes_events
#audit axioms Rumoca.FMI3.TensorInstanceRhs.field_outside
#audit axioms Rumoca.FMI3.TensorInstance.writable_output
#audit axioms Rumoca.FMI3.TensorInstanceJacobian.jacobian_writes_events


-- Tensor Float64 accessor bodies over the tensor instance record (package-checked
-- product; single-reference dispatch over all declared variables, printed-text
-- denotation; no production emission, no scalar-adapter or existing-contract change).
#audit axioms Rumoca.FMI3.TensorFloat64.getCopy_reaches
#audit axioms Rumoca.FMI3.TensorFloat64.setCopy_reaches
#audit axioms Rumoca.FMI3.TensorFloat64.getBody_closed
#audit axioms Rumoca.FMI3.TensorFloat64.setBody_closed
#audit axioms Rumoca.FMI3.TensorFloat64.validate_reaches
#audit axioms Rumoca.FMI3.TensorFloat64.get_reaches_of
#audit axioms Rumoca.FMI3.TensorFloat64.get_behaviors_time
#audit axioms Rumoca.FMI3.TensorFloat64.get_behaviors_input
#audit axioms Rumoca.FMI3.TensorFloat64.get_behaviors_state
#audit axioms Rumoca.FMI3.TensorFloat64.get_behaviors_deriv
#audit axioms Rumoca.FMI3.TensorFloat64.get_behaviors_output
#audit axioms Rumoca.FMI3.TensorFloat64.set_reaches_of
#audit axioms Rumoca.FMI3.TensorFloat64.set_behaviors_input
#audit axioms Rumoca.FMI3.TensorFloat64.set_behaviors_state
#audit axioms Rumoca.FMI3.TensorFloat64.null_get_behaviors
#audit axioms Rumoca.FMI3.TensorFloat64.null_set_behaviors
#audit axioms Rumoca.FMI3.TensorFloat64.reads_time
#audit axioms Rumoca.FMI3.TensorFloat64.reads_output
#audit axioms Rumoca.FMI3.TensorFloat64.writable_state
#audit axioms Rumoca.FMI3.TensorFloat64.inputWritableStore_writable
#audit axioms Rumoca.FMI3.TensorFloat64.get_instance_behaviors_time
#audit axioms Rumoca.FMI3.TensorFloat64.get_instance_behaviors_input
#audit axioms Rumoca.FMI3.TensorFloat64.get_instance_behaviors_state
#audit axioms Rumoca.FMI3.TensorFloat64.get_instance_behaviors_deriv
#audit axioms Rumoca.FMI3.TensorFloat64.get_instance_behaviors_output
#audit axioms Rumoca.FMI3.TensorFloat64.set_instance_behaviors_state
#audit axioms Rumoca.FMI3.TensorFloat64.set_instance_behaviors_input
#audit axioms Rumoca.FMI3.TensorFloat64.set_preserves_other_instances
#audit axioms Rumoca.FMI3.TensorFloat64.getBody_printable
#audit axioms Rumoca.FMI3.TensorFloat64.setBody_printable
#audit axioms Rumoca.FMI3.TensorFloat64.signature_printable
#audit axioms Rumoca.FMI3.TensorFloat64.getFunction_denotes
#audit axioms Rumoca.FMI3.TensorFloat64.setFunction_denotes
#audit axioms Rumoca.FMI3.TensorFloat64.get_contract
#audit axioms Rumoca.FMI3.TensorFloat64.set_contract
#audit axioms Rumoca.FMI3.TensorFloat64.get_fail_prefix
#audit axioms Rumoca.FMI3.TensorFloat64.set_fail_prefix
#audit axioms Rumoca.FMI3.TensorFloat64.get_fail_behaviors
#audit axioms Rumoca.FMI3.TensorFloat64.set_fail_behaviors

#audit axioms Rumoca.FMI3.TensorContinuousStates.parameters_bound
#audit axioms Rumoca.FMI3.TensorContinuousStates.count_pass
#audit axioms Rumoca.FMI3.TensorContinuousStates.getBody_closed
#audit axioms Rumoca.FMI3.TensorContinuousStates.setBody_closed
#audit axioms Rumoca.FMI3.TensorContinuousStates.get_reaches
#audit axioms Rumoca.FMI3.TensorContinuousStates.get_behaviors
#audit axioms Rumoca.FMI3.TensorContinuousStates.set_reaches
#audit axioms Rumoca.FMI3.TensorContinuousStates.set_behaviors
#audit axioms Rumoca.FMI3.TensorContinuousStates.null_get_behaviors
#audit axioms Rumoca.FMI3.TensorContinuousStates.null_set_behaviors
#audit axioms Rumoca.FMI3.TensorContinuousStates.get_instance_behaviors
#audit axioms Rumoca.FMI3.TensorContinuousStates.set_instance_behaviors
#audit axioms Rumoca.FMI3.TensorContinuousStates.set_preserves_other_instances
#audit axioms Rumoca.FMI3.TensorContinuousStates.signature_printable
#audit axioms Rumoca.FMI3.TensorContinuousStates.getBody_printable
#audit axioms Rumoca.FMI3.TensorContinuousStates.setBody_printable
#audit axioms Rumoca.FMI3.TensorContinuousStates.getFunction_denotes
#audit axioms Rumoca.FMI3.TensorContinuousStates.setFunction_denotes
#audit axioms Rumoca.FMI3.TensorContinuousStates.get_contract
#audit axioms Rumoca.FMI3.TensorContinuousStates.set_contract
#audit axioms Rumoca.FMI3.TensorContinuousStates.derivParameters_bound
#audit axioms Rumoca.FMI3.TensorContinuousStates.derivBody_closed
#audit axioms Rumoca.FMI3.TensorContinuousStates.deriv_delivers
#audit axioms Rumoca.FMI3.TensorContinuousStates.deriv_instance_delivers
#audit axioms Rumoca.FMI3.TensorContinuousStates.null_deriv_behaviors
#audit axioms Rumoca.FMI3.TensorContinuousStates.derivBody_printable
#audit axioms Rumoca.FMI3.TensorContinuousStates.derivSignature_printable
#audit axioms Rumoca.FMI3.TensorContinuousStates.derivFunction_denotes
#audit axioms Rumoca.FMI3.TensorContinuousStates.derivCount_pass
#audit axioms Rumoca.FMI3.TensorContinuousStates.deriv_enter
#audit axioms Rumoca.FMI3.TensorContinuousStates.deriv_reaches
#audit axioms Rumoca.FMI3.TensorContinuousStates.deriv_behaviors
#audit axioms Rumoca.FMI3.TensorContinuousStates.jac_enter
#audit axioms Rumoca.FMI3.TensorContinuousStates.deriv_output_reaches
#audit axioms Rumoca.FMI3.TensorContinuousStates.deriv_output_behaviors
#audit axioms Rumoca.FMI3.TensorContinuousStates.deriv_execution_free
#audit axioms Rumoca.FMI3.TensorContinuousStates.deriv_execution_output
#audit axioms Rumoca.FMI3.TensorContinuousStates.deriv_contract

#audit axioms Rumoca.CMemory.store_of_convert
#audit axioms Rumoca.FMI3.TensorCountQueries.count_bounded
#audit axioms Rumoca.FMI3.TensorCountQueries.body_closed
#audit axioms Rumoca.FMI3.TensorCountQueries.parameters_bound
#audit axioms Rumoca.FMI3.TensorCountQueries.store_count
#audit axioms Rumoca.FMI3.TensorCountQueries.pointer_pass
#audit axioms Rumoca.FMI3.TensorCountQueries.body_run
#audit axioms Rumoca.FMI3.TensorCountQueries.call_behaviors
#audit axioms Rumoca.FMI3.TensorCountQueries.null_behaviors
#audit axioms Rumoca.FMI3.TensorCountQueries.signature_printable
#audit axioms Rumoca.FMI3.TensorCountQueries.body_printable
#audit axioms Rumoca.FMI3.TensorCountQueries.function_denotes
#audit axioms Rumoca.FMI3.TensorCountQueries.contract

#audit axioms Rumoca.FMI3.TensorSetTime.body_closed
#audit axioms Rumoca.FMI3.TensorSetTime.parameters_bound
#audit axioms Rumoca.FMI3.TensorSetTime.finite_pass
#audit axioms Rumoca.FMI3.TensorSetTime.time_write
#audit axioms Rumoca.FMI3.TensorSetTime.body_run
#audit axioms Rumoca.FMI3.TensorSetTime.call_behaviors
#audit axioms Rumoca.FMI3.TensorSetTime.null_behaviors
#audit axioms Rumoca.FMI3.TensorSetTime.nonfinite_prefix
#audit axioms Rumoca.FMI3.TensorSetTime.nonfinite_behaviors
#audit axioms Rumoca.FMI3.TensorSetTime.preserves_other_instances
#audit axioms Rumoca.FMI3.TensorSetTime.signature_printable
#audit axioms Rumoca.FMI3.TensorSetTime.body_printable
#audit axioms Rumoca.FMI3.TensorSetTime.function_denotes
#audit axioms Rumoca.FMI3.TensorSetTime.contract

#audit axioms Rumoca.FMI3.TensorReset.zeroBody_closed
#audit axioms Rumoca.FMI3.TensorReset.state_ne_member
#audit axioms Rumoca.FMI3.TensorReset.zeroCopy_step
#audit axioms Rumoca.FMI3.TensorReset.putZero_step
#audit axioms Rumoca.FMI3.TensorReset.zeroCopy_reaches
#audit axioms Rumoca.FMI3.TensorReset.body_closed
#audit axioms Rumoca.FMI3.TensorReset.parameters_bound
#audit axioms Rumoca.FMI3.TensorReset.bookkeeping_reaches
#audit axioms Rumoca.FMI3.TensorReset.reset_reaches
#audit axioms Rumoca.FMI3.TensorReset.reset_behaviors
#audit axioms Rumoca.FMI3.TensorReset.null_behaviors
#audit axioms Rumoca.FMI3.TensorReset.reads_initialization
#audit axioms Rumoca.FMI3.TensorReset.reset_mode_instantiated
#audit axioms Rumoca.FMI3.TensorReset.initialization_is_zero
#audit axioms Rumoca.FMI3.TensorReset.preserves_other_instances
#audit axioms Rumoca.FMI3.TensorReset.signature_printable
#audit axioms Rumoca.FMI3.TensorReset.body_printable
#audit axioms Rumoca.FMI3.TensorReset.function_denotes
#audit axioms Rumoca.FMI3.TensorReset.contract

-- Tensor Model Exchange mode-transition bodies over the tensor instance record
-- (package-checked product; no production emission).
#audit axioms Rumoca.FMI3.TensorLifecycleModes.body_closed
#audit axioms Rumoca.FMI3.TensorLifecycleModes.parameters_bound
#audit axioms Rumoca.FMI3.TensorLifecycleModes.body_run
#audit axioms Rumoca.FMI3.TensorLifecycleModes.call_behaviors
#audit axioms Rumoca.FMI3.TensorLifecycleModes.null_behaviors
#audit axioms Rumoca.FMI3.TensorLifecycleModes.illegal_prefix
#audit axioms Rumoca.FMI3.TensorLifecycleModes.illegal_behaviors
#audit axioms Rumoca.FMI3.TensorLifecycleModes.preserves_other_instances
#audit axioms Rumoca.FMI3.TensorLifecycleModes.signature_printable
#audit axioms Rumoca.FMI3.TensorLifecycleModes.body_printable
#audit axioms Rumoca.FMI3.TensorLifecycleModes.function_denotes
#audit axioms Rumoca.FMI3.TensorLifecycleModes.contract
#audit axioms Rumoca.FMI3.TensorLifecycleModes.Phase.afterKind_of_ne_exit

-- Tensor fmi3FreeInstance over the static tensor instance pool (package-checked
-- product; reuses the shared model-agnostic release; no production emission).
#audit axioms Rumoca.FMI3.TensorFree.free_owned
#audit axioms Rumoca.FMI3.TensorFree.null_behaviors
#audit axioms Rumoca.FMI3.TensorFree.contract

-- Composed tensor lifecycle history over the static instance pool (package-checked
-- product; no production emission).
#audit axioms Rumoca.FMI3.TensorLifecycleHistory.lifecycle_history
#audit axioms Rumoca.FMI3.TensorLifecycleHistory.lifecycle_cs_step

-- Reserved tensor instance-record initializer (package-checked product; no
-- production emission).
#audit axioms Rumoca.FMI3.TensorInstanceInit.code_closed
#audit axioms Rumoca.FMI3.TensorInstanceInit.metaCode_run
#audit axioms Rumoca.FMI3.TensorInstanceInit.return_reaches
#audit axioms Rumoca.FMI3.TensorInstanceInit.complete
#audit axioms Rumoca.FMI3.TensorInstanceInit.initialized
#audit axioms Rumoca.FMI3.TensorInstanceInit.reads_state
#audit axioms Rumoca.FMI3.TensorInstanceInit.frame
#audit axioms Rumoca.FMI3.TensorInstanceInit.other_instance
#audit axioms Rumoca.FMI3.TensorInstanceInit.Storage.preserved

-- Tensor instance-creation reservation suffix over the static tensor pool
-- (package-checked product; no production emission).
#audit axioms Rumoca.FMI3.TensorFactory.reserve_entry
#audit axioms Rumoca.FMI3.TensorFactory.initialization_reaches
#audit axioms Rumoca.FMI3.TensorFactory.guarded_initialization
#audit axioms Rumoca.FMI3.TensorFactory.successful
#audit axioms Rumoca.FMI3.TensorFactory.exhausted_silent
#audit axioms Rumoca.FMI3.TensorFactory.initialized_owners
#audit axioms Rumoca.FMI3.TensorFactory.successful_owned
#audit axioms Rumoca.FMI3.TensorFactory.Created.release
#audit axioms Rumoca.FMI3.TensorFactory.create_release
#audit axioms Rumoca.FMI3.TensorFactory.admission_accepts
#audit axioms Rumoca.FMI3.TensorFactory.rejected_silent
#audit axioms Rumoca.FMI3.TensorFactory.contract

-- Tensor lifecycle history started from a proved creation call (package-checked
-- product; no production emission).
#audit axioms Rumoca.FMI3.TensorLifecycleHistory.lifecycle_from_creation

-- Tensor fmi3GetNominalsOfContinuousStates over the symbolic state volume
-- (package-checked product; no production emission).
#audit axioms Rumoca.FMI3.TensorNominals.oneBody_closed
#audit axioms Rumoca.FMI3.TensorNominals.oneCopy_step
#audit axioms Rumoca.FMI3.TensorNominals.oneCopy_reaches
#audit axioms Rumoca.FMI3.TensorNominals.body_closed
#audit axioms Rumoca.FMI3.TensorNominals.parameters_bound
#audit axioms Rumoca.FMI3.TensorNominals.count_pass
#audit axioms Rumoca.FMI3.TensorNominals.nominal_reaches
#audit axioms Rumoca.FMI3.TensorNominals.nominal_behaviors
#audit axioms Rumoca.FMI3.TensorNominals.null_behaviors
#audit axioms Rumoca.FMI3.TensorNominals.reads_nominals
#audit axioms Rumoca.FMI3.TensorNominals.preserves_instance
#audit axioms Rumoca.FMI3.TensorNominals.signature_printable
#audit axioms Rumoca.FMI3.TensorNominals.body_printable
#audit axioms Rumoca.FMI3.TensorNominals.function_denotes
#audit axioms Rumoca.FMI3.TensorNominals.contract

-- Tensor behavioral bodies reusing the model-independent scalar contracts over
-- the tensor instance record (package-checked products; no production emission).
-- Each `independent` root certifies the emitted function does not depend on the
-- prepared model, so the scalar contract transfers to the tensor instance record.
#audit axioms Rumoca.FMI3.TensorVersion.independent
#audit axioms Rumoca.FMI3.TensorVersion.contract
#audit axioms Rumoca.FMI3.TensorDebugLogging.independent
#audit axioms Rumoca.FMI3.TensorDebugLogging.denotation
#audit axioms Rumoca.FMI3.TensorDebugLogging.contract
#audit axioms Rumoca.FMI3.TensorScheduledCreation.independent
#audit axioms Rumoca.FMI3.TensorScheduledCreation.contract
#audit axioms Rumoca.FMI3.TensorDiscreteEvaluation.independent
#audit axioms Rumoca.FMI3.TensorDiscreteEvaluation.denotation
#audit axioms Rumoca.FMI3.TensorDiscreteEvaluation.contract
#audit axioms Rumoca.FMI3.TensorDiscreteUpdate.independent
#audit axioms Rumoca.FMI3.TensorDiscreteUpdate.denotation
#audit axioms Rumoca.FMI3.TensorDiscreteUpdate.contract
#audit axioms Rumoca.FMI3.TensorCompletedStep.independent
#audit axioms Rumoca.FMI3.TensorCompletedStep.denotation
#audit axioms Rumoca.FMI3.TensorCompletedStep.contract
#audit axioms Rumoca.FMI3.TensorEventIndicators.independent
#audit axioms Rumoca.FMI3.TensorEventIndicators.denotation
#audit axioms Rumoca.FMI3.TensorEventIndicators.contract

-- Tensor Co-Simulation fmi3DoStep internal Euler update over the symbolic state
-- volume (package-checked product; no production emission). The elementwise
-- x[k] = x[k] + dx[k] counted loop keeps each cell's finite-arithmetic outcome
-- explicit as an `Adds` premise.
#audit axioms Rumoca.FMI3.TensorDoStep.eulerBody_closed
#audit axioms Rumoca.FMI3.TensorDoStep.eulerStep
#audit axioms Rumoca.FMI3.TensorDoStep.euler_reaches
#audit axioms Rumoca.FMI3.TensorDoStep.euler_delivers
#audit axioms Rumoca.FMI3.TensorDoStep.store_writable_state
#audit axioms Rumoca.FMI3.TensorDoStep.internalStep_reaches

-- The prepared derivative entry over an arbitrary well-formed instance heap, and
-- the declaration-free per-internal-step body used by the Co-Simulation grid loop:
-- evaluate `rumoca_rhs` into `der(x)`, reset the inner counter, and run the
-- elementwise Euler update over the symbolic state volume. Every loop body is
-- declaration-free so `CBodyEmbedding.closedBlocks` holds function-wide.
#audit axioms Rumoca.FMI3.TensorDoStep.derivative_run
#audit axioms Rumoca.FMI3.TensorDoStep.stepBody_closed
#audit axioms Rumoca.FMI3.TensorDoStep.stepBody_noDecl
#audit axioms Rumoca.FMI3.TensorDoStep.internalStepPure_reaches
-- The N-fold Euler state iteration and the outer grid loop that iterates the
-- declaration-free internal step over the symbolic state volume: the state region
-- advances by the N-fold finite Euler step, the derivative region reads the last
-- result, and the input region and every other instance are preserved.
#audit axioms Rumoca.FMI3.TensorDoStep.eulerIterate_succ
#audit axioms Rumoca.FMI3.TensorDoStep.stepLoop_reaches

-- The per-internal-step time advance (advance the instance's scalar time base by
-- one, keeping the finite addition explicit as an `Adds` premise), the
-- time-augmented internal step, and the N-step grid loop that carries the state by
-- the N-fold Euler step and the time base to the N-fold finite sum `times N`.
#audit axioms Rumoca.FMI3.TensorDoStep.timeStep
#audit axioms Rumoca.FMI3.TensorDoStep.stepBodyT_closed
#audit axioms Rumoca.FMI3.TensorDoStep.stepBodyT_noDecl
#audit axioms Rumoca.FMI3.TensorDoStep.internalStepPureT_reaches
#audit axioms Rumoca.FMI3.TensorDoStep.stepLoopT_reaches

-- The complete guarded tensor `fmi3DoStep` body: the model-independent scalar
-- guard prefix of `Runtime.doStep` (through `stepGrid`) followed by the hoisted
-- declarations and the outer grid loop over the time-augmented internal step. The
-- whole function is a closed block (every loop body is declaration-free).
#audit axioms Rumoca.FMI3.TensorDoStep.doStepBody_prefix
#audit axioms Rumoca.FMI3.TensorDoStep.outerLoop_closed
#audit axioms Rumoca.FMI3.TensorDoStep.doStepBody_closed

-- The accepted tensor `fmi3DoStep` execution and its bundled tensor-native contract:
-- the model-dependent numerical tail as one observable execution (declarations, the
-- outer grid loop, the last-successful-time publication and the `fmi3OK` return), the
-- reused model-independent guard prefix, the accepted end-to-end reach/behaviors under
-- the guard and admitted-duration premises exactly as `StepGuards`/`StepAdmission`
-- expose them, the null-handle and lifecycle rejections, and the printed-text
-- denotation of the guarded body.
#audit axioms Rumoca.FMI3.TensorDoStep.field_index_block
#audit axioms Rumoca.FMI3.TensorDoStep.cell_block_ne
#audit axioms Rumoca.FMI3.TensorDoStep.tensorSolve_reaches
#audit axioms Rumoca.FMI3.TensorDoStep.tensorSolveOutput_reaches
#audit axioms Rumoca.FMI3.TensorDoStep.front_run
#audit axioms Rumoca.FMI3.TensorDoStep.accepted_reaches
#audit axioms Rumoca.FMI3.TensorDoStep.accepted_behaviors
#audit axioms Rumoca.FMI3.TensorDoStep.accepted_output_reaches
#audit axioms Rumoca.FMI3.TensorDoStep.accepted_output_behaviors
#audit axioms Rumoca.FMI3.TensorDoStep.null_behaviors
#audit axioms Rumoca.FMI3.TensorDoStep.lifecycle_behaviors

-- The pinned tensor floating-environment interface (`cInterface` plus the header
-- round-to-nearest macro) supplies the round-to-nearest guard constant and every
-- helper/status spelling the numerical tail resolves, so the accepted execution and
-- contract carry only the modeled `fegetround`/`floor` platform returns; and the
-- whole-call `fmi3Discard` for an off-grid or over-bound admitted step reaches the
-- shared discard block and returns `fmi3Discard` under both the suppressed and the
-- enabled logging outcomes, reusing the scalar `StepDiscard` composition.
#audit axioms Rumoca.FMI3.TensorDoStep.finishOK
#audit axioms Rumoca.FMI3.TensorDoStep.cInterface_fenv
#audit axioms Rumoca.FMI3.TensorDoStep.fenvInterface_fenv
#audit axioms Rumoca.FMI3.TensorDoStep.discard_prefix
#audit axioms Rumoca.FMI3.TensorDoStep.discard_suppressed_behaviors
#audit axioms Rumoca.FMI3.TensorDoStep.discard_logged_behaviors
#audit axioms Rumoca.FMI3.TensorDoStep.signature_printable
#audit axioms Rumoca.FMI3.TensorDoStep.body_printable
#audit axioms Rumoca.FMI3.TensorDoStep.function_denotes
#audit axioms Rumoca.FMI3.TensorDoStep.execution_free
#audit axioms Rumoca.FMI3.TensorDoStep.execution_output
#audit axioms Rumoca.FMI3.TensorDoStep.contract

-- Tensor FMI 3 adapter function list (package-checked product; no production
-- emission). Each pinned header signature renders its proved tensor behavioral
-- body (19 shape-dependent functions dispatched by name) or, for the seven
-- model-independent behavioral and the 49 unsupported/absent-type functions, the
-- same body the scalar renderer emits. The name multiset equals the scalar list's,
-- so distinctness, located positions, definition table and literal pool follow.
#audit axioms Rumoca.FMI3.TensorFunctions.tensorFunction_signature
#audit axioms Rumoca.FMI3.TensorFunctions.tensorFunction_name
#audit axioms Rumoca.FMI3.TensorFunctions.functions_names
#audit axioms Rumoca.FMI3.TensorFunctions.functions_signatures
#audit axioms Rumoca.FMI3.TensorFunctions.functions_nodup
#audit axioms Rumoca.FMI3.TensorFunctions.rendered_functions
#audit axioms Rumoca.FMI3.TensorFunctions.rendered_member
#audit axioms Rumoca.FMI3.TensorFunctions.rendered_helper
#audit axioms Rumoca.FMI3.TensorFunctions.definition_bound
#audit axioms Rumoca.FMI3.TensorFunctions.function_bound
#audit axioms Rumoca.FMI3.TensorFunctions.program_covered
#audit axioms Rumoca.FMI3.TensorFunctions.helpers_bound
#audit axioms Rumoca.FMI3.TensorFunctions.header_fresh
#audit axioms Rumoca.FMI3.TensorFunctions.text_bound
#audit axioms Rumoca.FMI3.TensorFunctions.pool_complete
-- The tensor helper prefix drops the dead scalar `model_rhs`/`model_advance`
-- wrappers; its names are a sublist of the scalar helper names. Call resolution
-- for the prepared kernel entry the tensor bodies call directly: it resolves in
-- the definition table (to the prepared RHS kernel when the header names are
-- disjoint from it), and its preamble prototype agrees with the derivative
-- arguments.
#audit axioms Rumoca.FMI3.TensorFunctions.helpers_subset
#audit axioms Rumoca.FMI3.TensorFunctions.scalar_names
#audit axioms Rumoca.FMI3.TensorFunctions.helper_names_sublist
#audit axioms Rumoca.FMI3.TensorFunctions.kernel_entry_resolves
#audit axioms Rumoca.FMI3.TensorFunctions.kernel_entry_is_kernel
#audit axioms Rumoca.FMI3.TensorFunctions.kernel_prototype_matches_args
#audit axioms Rumoca.FMI3.TensorFunctions.jacobian_prototype_matches_args

-- The two unsupported/absent-type family contracts over the tensor adapter list.
-- The family execution bodies are identical to the scalar renderer's; only the
-- surrounding function list and its literal pool differ. The model-agnostic
-- execution core is reused verbatim, so no family execution proof is duplicated.
#audit axioms Rumoca.FMI3.absent_function
#audit axioms Rumoca.FMI3.capability_function
#audit axioms Rumoca.FMI3.scheduled_function
#audit axioms Rumoca.FMI3.scalar_bound
#audit axioms Rumoca.FMI3.scalar_member
#audit axioms Rumoca.FMI3.TensorAbsentVariables.prepared_correct
#audit axioms Rumoca.FMI3.TensorAbsentVariables.rendered_contract
#audit axioms Rumoca.FMI3.TensorAbsentVariables.family_correct
#audit axioms Rumoca.FMI3.TensorCapabilityRejection.prepared_correct
#audit axioms Rumoca.FMI3.TensorCapabilityRejection.rendered_contract
#audit axioms Rumoca.FMI3.TensorCapabilityRejection.family_correct

-- The tensor storage preamble: the tensor instance record layout the tensor
-- bodies address (member names and region extents agree with `TensorInstance`),
-- and the storage section's tokenization under the shared C scanner. The header
-- inclusion block is the scalar preamble's, reused verbatim.
#audit axioms Rumoca.FMI3.TensorStorage.layout_names
#audit axioms Rumoca.FMI3.TensorStorage.layout_names_core
#audit axioms Rumoca.FMI3.TensorStorage.layout_state_extent
#audit axioms Rumoca.FMI3.TensorStorage.layout_output_extent
#audit axioms Rumoca.FMI3.TensorStorage.record_printed
#audit axioms Rumoca.FMI3.TensorStorage.storage_printed
#audit axioms Rumoca.FMI3.TensorStorage.declarations_header

-- The tensor adapter function-section grammar: the factory-body printability
-- (the one dispatched tensor body without a prior printability theorem), the
-- per-function printability dispatch, and the maximal-munch tokenization of the
-- whole function section as the tensor function list.
#audit axioms Rumoca.FMI3.TensorAdapterPrinter.factory_printable
#audit axioms Rumoca.FMI3.TensorAdapterPrinter.tensorFunction_printable
#audit axioms Rumoca.FMI3.TensorAdapterPrinter.functions_printable
#audit axioms Rumoca.FMI3.TensorAdapterPrinter.rendered_contract

-- The first tensor adapter contract skeleton: the rendered text of the function
-- list bound to the model-free public-API coverage, the two family contracts,
-- every proved tensor behavioral function contract, and the declaration-preamble
-- record-layout and identifier agreements, with `render_contract` proved.
#audit axioms Rumoca.FMI3.TensorAdapter.render_contract

-- Stage B1: the record profile and its constant-rate (no-input, no-output)
-- instance. The generic storage recovers the tensor profile as its input-present
-- instance and the constant profile as its input-absent, output-absent instance.
#audit axioms Rumoca.FMI3.TensorInstance.core_eq_opt
#audit axioms Rumoca.FMI3.TensorInstance.store_eq_opt
#audit axioms Rumoca.FMI3.TensorInstance.coreOpt_none
#audit axioms Rumoca.FMI3.TensorInstance.constantStore_eq_opt
#audit axioms Rumoca.FMI3.TensorInstance.constant_reads_state
#audit axioms Rumoca.FMI3.TensorInstance.constant_writable_derivative
#audit axioms Rumoca.FMI3.TensorInstance.constant_fields_separate
#audit axioms Rumoca.FMI3.TensorInstance.constant_instances_separate
#audit axioms Rumoca.FMI3.TensorInstance.constant_store_other_instance

-- Stage B1: the profile-generic storage declarations and the constant-rate
-- layout and tokenization.
#audit axioms Rumoca.FMI3.TensorStorage.regionMembers_eq
#audit axioms Rumoca.FMI3.TensorStorage.members_eq
#audit axioms Rumoca.FMI3.TensorStorage.recordRender_eq
#audit axioms Rumoca.FMI3.TensorStorage.storageRender_eq
#audit axioms Rumoca.FMI3.TensorStorage.declarations_eq
#audit axioms Rumoca.FMI3.TensorStorage.layout_names_constant
#audit axioms Rumoca.FMI3.TensorStorage.layout_state_extent_constant
#audit axioms Rumoca.FMI3.TensorStorage.recordG_printed
#audit axioms Rumoca.FMI3.TensorStorage.storageG_printed
#audit axioms Rumoca.FMI3.TensorStorage.declarationsG_header

-- Stage 3: the executable constant-rate kernel entries bound to the static
-- constant instance record. The list-indexed kernel view is bridged to the dense
-- tensor view, and the proved loop-call behaviors embed into the observable call
-- machine through the typed-to-observable transfer. Universal in the state shape,
-- the source rates and the pool index.
#audit axioms Rumoca.FMI3.ConstantInstanceRhs.valueGet
#audit axioms Rumoca.FMI3.ConstantInstanceRhs.ratesVec_get
#audit axioms Rumoca.FMI3.ConstantInstanceRhs.eulerVec_get
#audit axioms Rumoca.FMI3.ConstantInstanceRhs.stateList_get
#audit axioms Rumoca.FMI3.ConstantInstanceRhs.cells_index
#audit axioms Rumoca.FMI3.ConstantInstanceRhs.cells_reads
#audit axioms Rumoca.FMI3.ConstantInstanceRhs.cells_writable
#audit axioms Rumoca.FMI3.ConstantInstanceRhs.cells_of
#audit axioms Rumoca.FMI3.ConstantInstanceRhs.reads_writable_cell
#audit axioms Rumoca.FMI3.ConstantInstanceRhs.reads_writable_cells
#audit axioms Rumoca.FMI3.ConstantInstanceRhs.writableN_of
#audit axioms Rumoca.FMI3.ConstantInstanceRhs.ratesVec_agree
#audit axioms Rumoca.FMI3.ConstantInstanceRhs.kernelDefinitions_rhs
#audit axioms Rumoca.FMI3.ConstantInstanceRhs.kernelDefinitions_step
#audit axioms Rumoca.FMI3.ConstantInstanceRhs.kernelDefinitions_sample
#audit axioms Rumoca.FMI3.ConstantInstanceRhs.rhs_writes_events
#audit axioms Rumoca.FMI3.ConstantInstanceRhs.step_writes_events

-- Stage B1: the constant-rate reserved-record initializer reuses the shared
-- tensor initializer, which is profile-independent.
#audit axioms Rumoca.FMI3.ConstantInstanceInit.code_closed
#audit axioms Rumoca.FMI3.ConstantInstanceInit.initialized
#audit axioms Rumoca.FMI3.ConstantInstanceInit.reads_state
#audit axioms Rumoca.FMI3.ConstantInstanceInit.other_instance

-- Stage B1: the constant-rate profile model description, universal in the state
-- shape, with one array state variable, no input and no output.
#audit axioms Rumoca.FMI3.TensorMetadata.constantToken_attribute
#audit axioms Rumoca.FMI3.TensorMetadata.constantStateVar_valid
#audit axioms Rumoca.FMI3.TensorMetadata.constantDerivativeVar_valid
#audit axioms Rumoca.FMI3.TensorMetadata.constantVariableNodes_valid
#audit axioms Rumoca.FMI3.TensorMetadata.constantStructureNodes_valid
#audit axioms Rumoca.FMI3.TensorMetadata.constant_valid
#audit axioms Rumoca.FMI3.TensorMetadata.constant_document
#audit axioms Rumoca.FMI3.TensorMetadata.constantValueReferences_eq
#audit axioms Rumoca.FMI3.TensorMetadata.constantValueReferences_nodup
#audit axioms Rumoca.FMI3.TensorMetadata.constantStateVar_dim_product
#audit axioms Rumoca.FMI3.TensorMetadata.constantDerivativeVar_dim_product
#audit axioms Rumoca.FMI3.TensorMetadata.constant_derivative_references_state
#audit axioms Rumoca.FMI3.TensorMetadata.constant_structure_references_declared
#audit axioms Rumoca.FMI3.TensorMetadata.constant_structure_dependencies_empty
#audit axioms Rumoca.FMI3.TensorMetadata.constant_modelIdentifiers_decode

-- Stage B2: the constant-rate Float64 accessor bodies over references 0..2
-- (time, state, derivative), the state reference writable and the derivative
-- read-only, with no input and no output.
#audit axioms Rumoca.FMI3.ConstantFloat64.getBody_closed
#audit axioms Rumoca.FMI3.ConstantFloat64.setBody_closed
#audit axioms Rumoca.FMI3.ConstantFloat64.getFunction_denotes
#audit axioms Rumoca.FMI3.ConstantFloat64.setFunction_denotes
#audit axioms Rumoca.FMI3.ConstantFloat64.null_get_behaviors
#audit axioms Rumoca.FMI3.ConstantFloat64.null_set_behaviors
#audit axioms Rumoca.FMI3.ConstantFloat64.get_contract
#audit axioms Rumoca.FMI3.ConstantFloat64.set_contract

-- Stage B2: the constant-rate derivative getter body, calling the numerical
-- entry `rumoca_constant_rhs(&(m->dx[0]))` and copying the written derivative
-- region into the caller buffer.
#audit axioms Rumoca.FMI3.ConstantDerivative.derivBody_closed
#audit axioms Rumoca.FMI3.ConstantDerivative.derivFunction_denotes
#audit axioms Rumoca.FMI3.ConstantDerivative.null_deriv_behaviors
#audit axioms Rumoca.FMI3.ConstantDerivative.deriv_copy_delivers
#audit axioms Rumoca.FMI3.ConstantDerivative.deriv_instance_delivers
#audit axioms Rumoca.FMI3.ConstantDerivative.deriv_delivers_holds
-- Stage 3: the fused single-run derivative getter over the constant instance
-- record, composing the guard prefix, the constant kernel entry through the
-- typed-to-observable transfer, and the copy suffix into the getter's sole
-- terminating behavior.
#audit axioms Rumoca.FMI3.ConstantDerivative.constant_deriv_enter
#audit axioms Rumoca.FMI3.ConstantDerivative.deriv_reaches
#audit axioms Rumoca.FMI3.ConstantDerivative.deriv_behaviors
#audit axioms Rumoca.FMI3.ConstantDerivative.deriv_execution_holds
#audit axioms Rumoca.FMI3.ConstantDerivative.deriv_contract

-- Stage B2: the constant-rate Co-Simulation do-step body, reusing the scalar
-- guard prefix and calling `rumoca_constant_step(&(m->x[0]))` per internal step.
#audit axioms Rumoca.FMI3.ConstantDoStep.doStepBody_prefix
#audit axioms Rumoca.FMI3.ConstantDoStep.doStepBody_closed
#audit axioms Rumoca.FMI3.ConstantDoStep.function_denotes
#audit axioms Rumoca.FMI3.ConstantDoStep.null_behaviors
#audit axioms Rumoca.FMI3.ConstantDoStep.lifecycle_behaviors
-- Stage 3c: the accepted and discard cases as one observable execution.
#audit axioms Rumoca.FMI3.ConstantDoStep.cInterface_fenv
#audit axioms Rumoca.FMI3.ConstantDoStep.fenvInterface_fenv
#audit axioms Rumoca.FMI3.ConstantDoStep.constant_step_enter
#audit axioms Rumoca.FMI3.ConstantDoStep.internalStep_reaches
#audit axioms Rumoca.FMI3.ConstantDoStep.stepLoop_reaches
#audit axioms Rumoca.FMI3.ConstantDoStep.solve_reaches
#audit axioms Rumoca.FMI3.ConstantDoStep.front_run
#audit axioms Rumoca.FMI3.ConstantDoStep.accepted_reaches
#audit axioms Rumoca.FMI3.ConstantDoStep.accepted_behaviors
#audit axioms Rumoca.FMI3.ConstantDoStep.execution_free
#audit axioms Rumoca.FMI3.ConstantDoStep.discard_prefix
#audit axioms Rumoca.FMI3.ConstantDoStep.discard_suppressed_behaviors
#audit axioms Rumoca.FMI3.ConstantDoStep.discard_logged_behaviors
#audit axioms Rumoca.FMI3.ConstantDoStep.contract

-- Stage B4: the constant-rate adapter assembly. The dispatch maps each pinned
-- header signature to a constant-specific body or the profile-independent tensor
-- body at the constant state shape, over the reused helper prefix; the definition
-- table binds the listed functions and the three constant kernel entries.
#audit axioms Rumoca.FMI3.ConstantFunctions.constantFunction_signature
#audit axioms Rumoca.FMI3.ConstantFunctions.constantFunction_name
#audit axioms Rumoca.FMI3.ConstantFunctions.functions_names
#audit axioms Rumoca.FMI3.ConstantFunctions.functions_signatures
#audit axioms Rumoca.FMI3.ConstantFunctions.functions_nodup
#audit axioms Rumoca.FMI3.ConstantFunctions.rendered_functions
#audit axioms Rumoca.FMI3.ConstantFunctions.rendered_member
#audit axioms Rumoca.FMI3.ConstantFunctions.rendered_helper
#audit axioms Rumoca.FMI3.ConstantFunctions.definition_bound
#audit axioms Rumoca.FMI3.ConstantFunctions.function_bound
#audit axioms Rumoca.FMI3.ConstantFunctions.program_covered
#audit axioms Rumoca.FMI3.ConstantFunctions.helpers_bound
#audit axioms Rumoca.FMI3.ConstantFunctions.helpers_subset
#audit axioms Rumoca.FMI3.ConstantFunctions.header_fresh
#audit axioms Rumoca.FMI3.ConstantFunctions.text_bound
#audit axioms Rumoca.FMI3.ConstantFunctions.pool_complete
#audit axioms Rumoca.FMI3.ConstantFunctions.kernel_entry_resolves
#audit axioms Rumoca.FMI3.ConstantFunctions.kernel_entry_rhs
#audit axioms Rumoca.FMI3.ConstantFunctions.kernel_entry_step
#audit axioms Rumoca.FMI3.ConstantFunctions.kernel_entry_sample
#audit axioms Rumoca.FMI3.ConstantFunctions.program_extends_kernel
#audit axioms Rumoca.FMI3.ConstantFunctions.rhs_prototype_matches_args
#audit axioms Rumoca.FMI3.ConstantFunctions.step_prototype_matches_args

-- Stage B4: the two unsupported/absent-type family contracts over the constant
-- adapter list, re-plumbing the model-agnostic execution cores.
#audit axioms Rumoca.FMI3.constant_absent_function
#audit axioms Rumoca.FMI3.constant_capability_function
#audit axioms Rumoca.FMI3.constant_scheduled_function
#audit axioms Rumoca.FMI3.constant_scalar_bound
#audit axioms Rumoca.FMI3.constant_scalar_member
#audit axioms Rumoca.FMI3.ConstantAbsentVariables.prepared_correct
#audit axioms Rumoca.FMI3.ConstantAbsentVariables.rendered_contract
#audit axioms Rumoca.FMI3.ConstantAbsentVariables.family_correct
#audit axioms Rumoca.FMI3.ConstantCapabilityRejection.prepared_correct
#audit axioms Rumoca.FMI3.ConstantCapabilityRejection.rendered_contract
#audit axioms Rumoca.FMI3.ConstantCapabilityRejection.family_correct

-- Stage B4: the constant adapter function-section grammar and the adapter contract
-- binding the rendered text to every per-function contract, both families, the
-- coverage, the call policy witnesses and the layout/identifier/token agreements.
#audit axioms Rumoca.FMI3.ConstantAdapterPrinter.constantFunction_printable
#audit axioms Rumoca.FMI3.ConstantAdapterPrinter.functions_printable
#audit axioms Rumoca.FMI3.ConstantAdapterPrinter.rendered_contract
#audit axioms Rumoca.FMI3.ConstantAdapter.render_contract
