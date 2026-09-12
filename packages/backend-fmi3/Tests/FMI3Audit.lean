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
#audit axioms Rumoca.FMI3.Reset.rendered_member

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
