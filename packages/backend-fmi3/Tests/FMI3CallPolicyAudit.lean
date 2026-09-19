import RumocaFMI3.ControlledInitialization
import RumocaFMI3.RetainedInitialization
import RumocaFMI3.PrivateWriteFrame
import RumocaFMI3.ClearedOrigins
import RumocaFMI3.ResourcePublication
import RumocaFMI3.InstanceAuthorityActions
import RumocaFMI3.InitializedAuthority
import RumocaFMI3.AuthorizedReleaseHistories
import RumocaFMI3.PublicationMemory
import RumocaFMI3.PublicationTransitions
import RumocaFMI3.PublicationProjection
import RumocaFMI3.ReleaseTail
import RumocaFMI3.InitializedPublication
import RumocaFMI3.HostInstanceStorage
import RumocaFMI3.InitializationHistory
import RumocaFMI3.InitializationIsolation
import RumocaFMI3.ExchangeInitialization
import RumocaFMI3.ReservationRegistryRuntime
import RumocaFMI3.InitializationFootprint
import RumocaFMI3.FactoryHistory
import RumocaFMI3.ScanReadyOutcome
import RumocaFMI3.ScanOnce
import RumocaFMI3.ReservationClaimOrigins
import RumocaFMI3.ScanClaimOutcome
import RumocaFMI3.FactoryAfterScan
import RumocaFMI3.SubcallDomain
import RumocaFMI3.HostCallPolicy
import RumocaFMI3.InitialRecordedExecution
import RumocaFMI3.ReservationOriginRuntime
import RumocaFMI3.AtomicFlagFrame
import RumocaFMI3.ReleaseConcurrentInvariant
import RumocaFMI3.ReleaseClaims
import RumocaFMI3.AtomicCallExecution
import RumocaFMI3.FactoryScanEntry
import RumocaFMI3.ReservationClaims
import RumocaFMI3.ConcurrentSlotHistories
import RumocaFMI3.AtomicCallRuntime
import RumocaFMI3.RuntimeStorage
import RumocaFMI3.StateSetterPolicy
import RumocaFMI3.RuntimeLinkage
import RumocaFMI3.CallPolicy
import RumocaFMI3.TensorCallPolicy
import RumocaFMI3.ConstantCallPolicy
import ProofAudit.Audit

/-! Independently cached formal audits for the call policy; no example-based tests. -/

#audit axioms Rumoca.FMI3.TensorCallPolicy.body_admits
#audit axioms Rumoca.FMI3.TensorCallPolicy.funcs_acceptedT
#audit axioms Rumoca.FMI3.TensorCallPolicy.acceptedT_noHeap
#audit axioms Rumoca.FMI3.TensorCallPolicy.tensor_no_heap
#audit axioms Rumoca.FMI3.TensorCallPolicy.classifiedT_rank
#audit axioms Rumoca.FMI3.TensorCallPolicy.body_rankT
#audit axioms Rumoca.FMI3.TensorCallPolicy.functions_rankT
#audit axioms Rumoca.FMI3.TensorCallPolicy.functions_isSomeT
#audit axioms Rumoca.FMI3.TensorCallPolicy.tensor_acyclic

-- Stage B4: the constant-rate adapter call graph is no-heap and acyclic over the
-- constant boundary set (the three constant kernel entries in the kernel role).
#audit axioms Rumoca.FMI3.ConstantCallPolicy.body_admits
#audit axioms Rumoca.FMI3.ConstantCallPolicy.funcs_acceptedC
#audit axioms Rumoca.FMI3.ConstantCallPolicy.acceptedC_noHeap
#audit axioms Rumoca.FMI3.ConstantCallPolicy.constant_no_heap
#audit axioms Rumoca.FMI3.ConstantCallPolicy.classifiedC_rank
#audit axioms Rumoca.FMI3.ConstantCallPolicy.body_rankC
#audit axioms Rumoca.FMI3.ConstantCallPolicy.functions_rankC
#audit axioms Rumoca.FMI3.ConstantCallPolicy.functions_isSomeC
#audit axioms Rumoca.FMI3.ConstantCallPolicy.constant_acyclic

#audit axioms Rumoca.FMI3.CallPolicy.body_policy
#audit axioms Rumoca.FMI3.CallPolicy.helpers_policy
#audit axioms Rumoca.FMI3.CallPolicy.functions_policy
#audit axioms Rumoca.FMI3.CallPolicy.classified_rank
#audit axioms Rumoca.FMI3.CallPolicy.body_rank
#audit axioms Rumoca.FMI3.CallPolicy.helpers_rank
#audit axioms Rumoca.FMI3.CallPolicy.functions_rank
#audit axioms Rumoca.FMI3.CallPolicy.entry_rank
#audit axioms Rumoca.FMI3.CallPolicy.covered_ranks
#audit axioms Rumoca.FMI3.CallPolicy.program_tree_name
#audit axioms Rumoca.FMI3.CallPolicy.program_rank
#audit axioms Rumoca.FMI3.CallPolicy.complete_program_no_cycle

#audit axioms Rumoca.FMI3.RuntimeLinkage.linked_contract
#audit axioms Rumoca.FMI3.RuntimeLinkage.logged_call_decreases
#audit axioms Rumoca.FMI3.RuntimeLinkage.logged_contract
#audit axioms Rumoca.FMI3.RuntimeLinkage.logged_execution_depth
#audit axioms Rumoca.FMI3.RuntimeLinkage.rank_bounded
#audit axioms Rumoca.FMI3.RuntimeLinkage.static_fresh
#audit axioms Rumoca.FMI3.RuntimeLinkage.static_unranked
#audit axioms Rumoca.FMI3.RuntimeLinkage.unranked_undefined
#audit axioms Rumoca.FMI3.RuntimeLinkage.withLogger_contract

#audit axioms Rumoca.FMI3.RuntimeStorage.linked_storage
#audit axioms Rumoca.FMI3.RuntimeStorage.logged_change_origin
#audit axioms Rumoca.FMI3.RuntimeStorage.logged_resources
#audit axioms Rumoca.FMI3.RuntimeStorage.logged_storage
#audit axioms Rumoca.FMI3.RuntimeStorage.logger_change
#audit axioms Rumoca.FMI3.RuntimeStorage.logger_storage
#audit axioms Rumoca.FMI3.RuntimeStorage.static_library
#audit axioms Rumoca.FMI3.StateSetterPolicy.StateDeclaration.unique
#audit axioms Rumoca.FMI3.StateSetterPolicy.artifact_modes
#audit axioms Rumoca.FMI3.StateSetterPolicy.continuous_state
#audit axioms Rumoca.FMI3.StateSetterPolicy.cs_state_simulation
#audit axioms Rumoca.FMI3.StateSetterPolicy.event_state
#audit axioms Rumoca.FMI3.StateSetterPolicy.writable_declaration
#audit axioms Rumoca.FMI3.StateSetterPolicy.writable_guard
#audit axioms Rumoca.FMI3.StateSetterPolicy.writable_modes

#audit axioms Rumoca.FMI3.AtomicCallPolicy.arguments_value
#audit axioms Rumoca.FMI3.AtomicCallPolicy.body_policy
#audit axioms Rumoca.FMI3.AtomicCallPolicy.boolean_eval
#audit axioms Rumoca.FMI3.AtomicCallPolicy.check_correct
#audit axioms Rumoca.FMI3.AtomicCallPolicy.entry_valid
#audit axioms Rumoca.FMI3.AtomicCallPolicy.exchange_value
#audit axioms Rumoca.FMI3.AtomicCallPolicy.functions_policy
#audit axioms Rumoca.FMI3.AtomicCallPolicy.helpers_policy
#audit axioms Rumoca.FMI3.AtomicCallPolicy.logged_concurrent_reaches
#audit axioms Rumoca.FMI3.AtomicCallPolicy.logged_named_only
#audit axioms Rumoca.FMI3.AtomicCallPolicy.logged_reaches
#audit axioms Rumoca.FMI3.AtomicCallPolicy.operand_sound
#audit axioms Rumoca.FMI3.AtomicCallPolicy.program_policy
#audit axioms Rumoca.FMI3.AtomicCallPolicy.ranked_entry
#audit axioms Rumoca.FMI3.AtomicCallPolicy.release_value
#audit axioms Rumoca.FMI3.ConcurrentSlots.Claim.target
#audit axioms Rumoca.FMI3.ConcurrentSlots.ScheduledStep.erases
#audit axioms Rumoca.FMI3.ConcurrentSlots.ScheduledStep.refines
#audit axioms Rumoca.FMI3.ConcurrentSlots.claim_busy
#audit axioms Rumoca.FMI3.ConcurrentSlots.claim_success
#audit axioms Rumoca.FMI3.ConcurrentSlots.history_refines
#audit axioms Rumoca.FMI3.ConcurrentSlots.owner_history_keeps
#audit axioms Rumoca.FMI3.ConcurrentSlots.owner_step_keeps
#audit axioms Rumoca.FMI3.ConcurrentSlots.reclaim_requires_release
#audit axioms Rumoca.FMI3.ConcurrentSlots.release_scheduled
#audit axioms Rumoca.FMI3.ConcurrentSlots.reserve_operation
#audit axioms Rumoca.FMI3.ConcurrentSlots.reserve_scheduled
#audit axioms Rumoca.FMI3.ConcurrentSlots.scheduled_reclaim_requires_release

#audit axioms Rumoca.FMI3.AtomicCallPolicy.exchange_scheduled
#audit axioms Rumoca.FMI3.AtomicCallPolicy.operations_of_values
#audit axioms Rumoca.FMI3.AtomicCallPolicy.release_scheduled
#audit axioms Rumoca.FMI3.ConcurrentSlots.bounded_reservation_claim
#audit axioms Rumoca.FMI3.StaticFactory.header_factory_scope
#audit axioms Rumoca.FMI3.StaticFactory.header_reserve_entry

#audit axioms Rumoca.FMI3.AtomicFlagFrame.linked_flags
#audit axioms Rumoca.FMI3.AtomicFlagFrame.logged_changed_origin
#audit axioms Rumoca.FMI3.AtomicFlagFrame.logged_exceptions
#audit axioms Rumoca.FMI3.AtomicFlagFrame.logged_flags
#audit axioms Rumoca.FMI3.AtomicFlagFrame.logged_step
#audit axioms Rumoca.FMI3.AtomicFlagFrame.static_library
#audit axioms Rumoca.FMI3.ConcurrentSlots.release_for_slot
#audit axioms Rumoca.FMI3.StaticRelease.ConcurrentInvariant.Metadata.preserved
#audit axioms Rumoca.FMI3.StaticRelease.ConcurrentInvariant.MetadataFrame.refl
#audit axioms Rumoca.FMI3.StaticRelease.ConcurrentInvariant.Ready.atomic_origin
#audit axioms Rumoca.FMI3.StaticRelease.ConcurrentInvariant.Ready.exit_value
#audit axioms Rumoca.FMI3.StaticRelease.ConcurrentInvariant.Ready.withHeap
#audit axioms Rumoca.FMI3.StaticRelease.ConcurrentInvariant.call_prefix_origin
#audit axioms Rumoca.FMI3.StaticRelease.ConcurrentInvariant.step_ready
#audit axioms Rumoca.FMI3.StaticRelease.ConcurrentInvariant.thread_reaches
#audit axioms Rumoca.FMI3.StaticRelease.ConcurrentInvariant.thread_step

#audit axioms Rumoca.FMI3.AtomicCallPolicy.logged_host_history
#audit axioms Rumoca.FMI3.ReservationOrigin.body_policy
#audit axioms Rumoca.FMI3.ReservationOrigin.entry_allowed
#audit axioms Rumoca.FMI3.ReservationOrigin.event_ready
#audit axioms Rumoca.FMI3.ReservationOrigin.excluded
#audit axioms Rumoca.FMI3.ReservationOrigin.functions_policy
#audit axioms Rumoca.FMI3.ReservationOrigin.helpers_policy
#audit axioms Rumoca.FMI3.ReservationOrigin.logged_controls
#audit axioms Rumoca.FMI3.ReservationOrigin.logged_host_origins
#audit axioms Rumoca.FMI3.ReservationOrigin.logged_named_only
#audit axioms Rumoca.FMI3.ReservationOrigin.operand_sound
#audit axioms Rumoca.FMI3.ReservationOrigin.program_policy
#audit axioms Rumoca.FMI3.ReservationOrigin.root_excluded
#audit axioms Rumoca.FMI3.ReservationOrigin.root_heap
#audit axioms Rumoca.FMI3.StaticRuntime.initial_recorded

#audit axioms Rumoca.FMI3.ConcurrentSlots.recorded_claim
#audit axioms Rumoca.FMI3.ConcurrentSlots.scan_claim_outcome
#audit axioms Rumoca.FMI3.ReservationOrigin.factory_return_closed
#audit axioms Rumoca.FMI3.ReservationOrigin.factory_suffix_closed
#audit axioms Rumoca.FMI3.ReservationOrigin.factory_suffix_history
#audit axioms Rumoca.FMI3.ReservationOrigin.logged_claim_origins
#audit axioms Rumoca.FMI3.ReservationOrigin.logged_factory_suffix
#audit axioms Rumoca.FMI3.ReservationOrigin.logged_subcall_domain
#audit axioms Rumoca.FMI3.ReservationOrigin.subcall_domain

#audit axioms Rumoca.FMI3.ConcurrentSlots.post_claim_call
#audit axioms Rumoca.FMI3.ConcurrentSlots.post_claim_heap
#audit axioms Rumoca.FMI3.ConcurrentSlots.post_claim_history
#audit axioms Rumoca.FMI3.ConcurrentSlots.post_claim_step
#audit axioms Rumoca.FMI3.ConcurrentSlots.scan_once
#audit axioms Rumoca.FMI3.ConcurrentSlots.scan_ready_outcome
#audit axioms Rumoca.FMI3.FactoryControl.Control.atomic_origin
#audit axioms Rumoca.FMI3.FactoryControl.Control.withHeap
#audit axioms Rumoca.FMI3.FactoryControl.control_step
#audit axioms Rumoca.FMI3.FactoryControl.logged_host_atomic
#audit axioms Rumoca.FMI3.FactoryControl.recorded_controls
#audit axioms Rumoca.FMI3.FactoryControl.root_heap
#audit axioms Rumoca.FMI3.FactoryRejection.Control.call_allowed
#audit axioms Rumoca.FMI3.FactoryRejection.Control.withHeap
#audit axioms Rumoca.FMI3.FactoryRejection.control_step
#audit axioms Rumoca.FMI3.FactoryValidation.actual_guard
#audit axioms Rumoca.FMI3.FactoryValidation.actual_resume
#audit axioms Rumoca.FMI3.FactoryValidation.header_reservation_after_identity
#audit axioms Rumoca.FMI3.FactoryValidation.resume_next

#audit axioms Rumoca.FMI3.ClearCallPolicy.body_policy
#audit axioms Rumoca.FMI3.ClearCallPolicy.helpers_policy
#audit axioms Rumoca.FMI3.ClearCallPolicy.logged_history
#audit axioms Rumoca.FMI3.ClearCallPolicy.logged_named_only
#audit axioms Rumoca.FMI3.ClearCallPolicy.operand_sound
#audit axioms Rumoca.FMI3.ClearCallPolicy.program_policy
#audit axioms Rumoca.FMI3.ClearCallPolicy.public_entry
#audit axioms Rumoca.FMI3.InstanceInitialization.field_assignment_footprint
#audit axioms Rumoca.FMI3.InstanceInitialization.initialization_footprint
#audit axioms Rumoca.FMI3.InstanceInitialization.slot_initialization_footprint
#audit axioms Rumoca.FMI3.ReservationRegistry.Step.erases
#audit axioms Rumoca.FMI3.ReservationRegistry.claim_represents
#audit axioms Rumoca.FMI3.ReservationRegistry.clearAt_outside
#audit axioms Rumoca.FMI3.ReservationRegistry.clearAt_slot
#audit axioms Rumoca.FMI3.ReservationRegistry.clear_represents
#audit axioms Rumoca.FMI3.ReservationRegistry.executeUpdate_ordinary
#audit axioms Rumoca.FMI3.ReservationRegistry.execute_represents
#audit axioms Rumoca.FMI3.ReservationRegistry.history_erases
#audit axioms Rumoca.FMI3.ReservationRegistry.history_lift
#audit axioms Rumoca.FMI3.ReservationRegistry.history_represents
#audit axioms Rumoca.FMI3.ReservationRegistry.logged_ready
#audit axioms Rumoca.FMI3.ReservationRegistry.logged_reservations
#audit axioms Rumoca.FMI3.ReservationRegistry.slotAt_address
#audit axioms Rumoca.FMI3.ReservationRegistry.slotAt_sound
#audit axioms Rumoca.FMI3.ReservationRegistry.step_represents

#audit axioms Rumoca.FMI3.InstanceInitialization.Initialized.region
#audit axioms Rumoca.FMI3.InstanceInitialization.Storage.region
#audit axioms Rumoca.FMI3.InstanceSlot.initialization_history
#audit axioms Rumoca.FMI3.InstanceSlot.initialization_observed
#audit axioms Rumoca.FMI3.InstanceSlot.initialization_other_instance
#audit axioms Rumoca.FMI3.InstanceSlot.initialization_ready
#audit axioms Rumoca.FMI3.InstanceSlot.initialized_region
#audit axioms Rumoca.FMI3.InstanceSlot.run_return
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.Ready.halted
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.Ready.withHeap
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.claimed_history
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.claimed_observed
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.exchange_initialization
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.step_other_instance
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.step_ready
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.step_with_frame

#audit axioms Rumoca.FMI3.PublicationRegistry.Step.erases
#audit axioms Rumoca.FMI3.PublicationRegistry.Step.reservations
#audit axioms Rumoca.FMI3.PublicationRegistry.advance_claim_free
#audit axioms Rumoca.FMI3.PublicationRegistry.advance_clear
#audit axioms Rumoca.FMI3.PublicationRegistry.advance_origin
#audit axioms Rumoca.FMI3.PublicationRegistry.advance_void_completion
#audit axioms Rumoca.FMI3.PublicationRegistry.claimed_publication
#audit axioms Rumoca.FMI3.PublicationRegistry.history_checked
#audit axioms Rumoca.FMI3.PublicationRegistry.history_erases
#audit axioms Rumoca.FMI3.PublicationRegistry.history_lift
#audit axioms Rumoca.FMI3.PublicationRegistry.history_publication_origin
#audit axioms Rumoca.FMI3.PublicationRegistry.history_represents
#audit axioms Rumoca.FMI3.PublicationRegistry.history_reservations
#audit axioms Rumoca.FMI3.PublicationRegistry.observe_origin
#audit axioms Rumoca.FMI3.PublicationRegistry.observe_owned
#audit axioms Rumoca.FMI3.PublicationRegistry.publish_origin
#audit axioms Rumoca.FMI3.PublicationRegistry.publish_owned
#audit axioms Rumoca.FMI3.PublicationRegistry.publish_wrong_lease
#audit axioms Rumoca.FMI3.PublicationRegistry.published_reservation
#audit axioms Rumoca.FMI3.PublicationRegistry.reservation_history_lift
#audit axioms Rumoca.FMI3.PublicationRegistry.reservations_advance
#audit axioms Rumoca.FMI3.PublicationRegistry.reservations_observe
#audit axioms Rumoca.FMI3.PublicationRegistry.reservations_publish
#audit axioms Rumoca.FMI3.PublicationRegistry.reservations_synchronize
#audit axioms Rumoca.FMI3.PublicationRegistry.step_publication_origin
#audit axioms Rumoca.FMI3.PublicationRegistry.synchronize_claim_busy
#audit axioms Rumoca.FMI3.PublicationRegistry.synchronize_claim_free
#audit axioms Rumoca.FMI3.PublicationRegistry.synchronize_clear
#audit axioms Rumoca.FMI3.PublicationRegistry.synchronize_cleared
#audit axioms Rumoca.FMI3.PublicationRegistry.synchronize_new
#audit axioms Rumoca.FMI3.PublicationRegistry.synchronize_published
#audit axioms Rumoca.FMI3.PublicationRegistry.synchronize_reservations
#audit axioms Rumoca.FMI3.RuntimeStorage.logged_host_storage
#audit axioms Rumoca.FMI3.RuntimeStorage.logged_initial_slots
#audit axioms Rumoca.FMI3.StaticRelease.clear_return_tail
#audit axioms Rumoca.FMI3.StaticRelease.return_tail_observed

#audit axioms Rumoca.FMI3.InstanceAuthority.authorized_clear
#audit axioms Rumoca.FMI3.InstanceAuthority.captured_authorized_clear
#audit axioms Rumoca.FMI3.InstanceAuthority.clear_iff
#audit axioms Rumoca.FMI3.InstanceAuthority.clear_linked
#audit axioms Rumoca.FMI3.InstanceAuthority.clear_vacant
#audit axioms Rumoca.FMI3.InstanceAuthority.complete_client
#audit axioms Rumoca.FMI3.InstanceAuthority.complete_linked
#audit axioms Rumoca.FMI3.InstanceAuthority.complete_other_call
#audit axioms Rumoca.FMI3.InstanceAuthority.complete_owned
#audit axioms Rumoca.FMI3.InstanceAuthority.complete_releasing
#audit axioms Rumoca.FMI3.InstanceAuthority.enter_iff
#audit axioms Rumoca.FMI3.InstanceAuthority.enter_linked
#audit axioms Rumoca.FMI3.InstanceAuthority.enter_other
#audit axioms Rumoca.FMI3.InstanceAuthority.entered_excludes
#audit axioms Rumoca.FMI3.InstanceAuthority.factory_complete
#audit axioms Rumoca.FMI3.InstanceAuthority.handle_erasure
#audit axioms Rumoca.FMI3.InstanceAuthority.initialized_handle
#audit axioms Rumoca.FMI3.InstanceAuthority.private_vacant
#audit axioms Rumoca.FMI3.InstanceAuthority.publish_iff
#audit axioms Rumoca.FMI3.InstanceAuthority.publish_linked
#audit axioms Rumoca.FMI3.InstanceAuthority.published_owns
#audit axioms Rumoca.FMI3.InstanceAuthority.release_enter
#audit axioms Rumoca.FMI3.InstanceAuthority.releasing_reservation
#audit axioms Rumoca.FMI3.InstanceAuthority.stale_rejected
#audit axioms Rumoca.FMI3.StaticRelease.Capture.atomic_control
#audit axioms Rumoca.FMI3.StaticRelease.Capture.captured_footprint
#audit axioms Rumoca.FMI3.StaticRelease.Capture.history_protected
#audit axioms Rumoca.FMI3.StaticRelease.Capture.needsMetadata_withHeap
#audit axioms Rumoca.FMI3.StaticRelease.Capture.protected_frame
#audit axioms Rumoca.FMI3.StaticRelease.Capture.step_protected
#audit axioms Rumoca.FMI3.StaticRelease.Capture.tail_footprint

#audit axioms Rumoca.FMI3.InstanceAuthority.CallOrigin.map
#audit axioms Rumoca.FMI3.InstanceAuthority.CallOrigin.retire
#audit axioms Rumoca.FMI3.InstanceAuthority.CallOrigins.arguments
#audit axioms Rumoca.FMI3.InstanceAuthority.Linked.claim
#audit axioms Rumoca.FMI3.InstanceAuthority.Linked.execute
#audit axioms Rumoca.FMI3.InstanceAuthority.NoTicket.clear
#audit axioms Rumoca.FMI3.InstanceAuthority.NoTicket.completeUse
#audit axioms Rumoca.FMI3.InstanceAuthority.NoTicket.enter
#audit axioms Rumoca.FMI3.InstanceAuthority.NoTicket.publish
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Change.linked
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.Step.invariant
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.Step.publications
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.Step.resources
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.history_invariant
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.initial_handle_origin
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.initial_history
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Step.erases
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.clear_retires
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.history_erases
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.history_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.history_retired
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.initial_history_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.released_history_complete
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.step_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.step_retired
#audit axioms Rumoca.FMI3.InstanceAuthority.borrowing_from_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.captured_release_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.clear_call_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.cleared_no_ticket
#audit axioms Rumoca.FMI3.InstanceAuthority.complete_argument_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.complete_call_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.complete_frame
#audit axioms Rumoca.FMI3.InstanceAuthority.complete_without_ticket
#audit axioms Rumoca.FMI3.InstanceAuthority.empty_argument_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.empty_call_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.enter_argument_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.enter_call_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.factory_complete_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.factory_no_ticket
#audit axioms Rumoca.FMI3.InstanceAuthority.idle_call_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.method_complete
#audit axioms Rumoca.FMI3.InstanceAuthority.method_complete_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.method_enter
#audit axioms Rumoca.FMI3.InstanceAuthority.method_enter_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.method_observation
#audit axioms Rumoca.FMI3.InstanceAuthority.null_release_no_ticket
#audit axioms Rumoca.FMI3.InstanceAuthority.publish_call_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.release_enter_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.released_complete_origins
#audit axioms Rumoca.FMI3.InstanceAuthority.ticket_unique
#audit axioms Rumoca.FMI3.InstanceAuthority.unowned_observation
#audit axioms Rumoca.FMI3.PublicAPI.ordinary_iff
#audit axioms Rumoca.FMI3.PublicAPI.ordinary_signature

#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.FactoryResult.returned
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.Step.private_reservation
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.claim_keeps
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.clear_keeps
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.complete_keeps
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.execute_keeps
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.framed_history
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.history_private_reservation
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.initialized_from_history
#audit axioms Rumoca.FMI3.InstanceAuthority.concurrent_preserves_private
#audit axioms Rumoca.FMI3.InstanceAuthority.event_preserves_private
#audit axioms Rumoca.FMI3.InstanceAuthority.internal_preserves_private
#audit axioms Rumoca.FMI3.InstanceAuthority.owned_writes_avoid_private
#audit axioms Rumoca.FMI3.InstanceAuthority.private_record_separate
#audit axioms Rumoca.FMI3.InstanceAuthority.store_preserves_private

#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.borrowed_writable
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.complete_controls
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.complete_writable_other
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.controlled_history
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.controls_erases
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.controls_private
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.exchange_controls
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.initialized_from_controls
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.initializer_controls
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.invoke_controls
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.invoke_writable_other
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.release_controls
#audit axioms Rumoca.FMI3.InstanceAuthority.Resources.Publication.writable_excludes_private
#audit axioms Rumoca.FMI3.InstanceAuthority.complete_preserves_ticket
#audit axioms Rumoca.FMI3.PublicationRegistry.reserved_records_separate
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.Ready.destination
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.Ready.foreign_frame
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.step_preserves_other_private
