import RumocaC.InvocationRetention
import RumocaC.WriteRegions
import RumocaC.InvocationIdentity
import RumocaC.InvocationFootprint
import RumocaC.VoidReturn
import RumocaC.HostStoreInvariant
import RumocaC.InitializationProgress
import RumocaC.InvocationRegion
import RumocaC.AtomicClaimProgress
import RumocaC.AtomicOperationSteps
import RumocaC.InvocationReplay
import RumocaC.AssignmentFootprint
import RumocaC.CallContextBoundary
import RumocaC.BooleanConversion
import RumocaC.AtomicScanClaimState
import RumocaC.InvocationContinuation
import RumocaC.AtomicScanClaimHistory
import RumocaC.CallContextHistory
import RumocaC.HostCallSites
import RumocaC.InvocationOrigins
import RumocaC.InvocationExecution
import RumocaC.CallSubprogram
import RumocaC.InvocationControl
import RumocaC.CallFrameClassification
import RumocaC.AtomicLoadedFrame
import RumocaC.CallHeapIntervals
import RumocaC.AtomicArguments
import RumocaC.AtomicScanEntryInvariant
import RumocaC.ConcurrentSteps
import RumocaC.CallSites
import RumocaC.CallStoreInvariant
import RumocaC.StorageLibrary
import RumocaC.CallPolicyExecution
import RumocaC.CallLinkage
import RumocaC.CallDepth
import RumocaC.CallPolicyProofs
import ProofAudit.Audit

/-! Independently cached formal audits for the call policy; no example-based tests. -/

#audit axioms Rumoca.CCallPolicy.expression_calls_complete
#audit axioms Rumoca.CCallPolicy.statement_calls_complete
#audit axioms Rumoca.CCallPolicy.checkExpression_correct
#audit axioms Rumoca.CCallPolicy.checkStatement_correct
#audit axioms Rumoca.CCallPolicy.checkFunction_correct
#audit axioms Rumoca.CCallPolicy.checkFunction_inventory
#audit axioms Rumoca.CCallPolicy.checked_operand
#audit axioms Rumoca.CCallPolicy.named_origin
#audit axioms Rumoca.CCallPolicy.checked_named_target
#audit axioms Rumoca.CCallPolicy.loop_ready_next
#audit axioms Rumoca.CCallPolicy.loop_ready_reaches
#audit axioms Rumoca.CCallPolicy.rank_callee_correct
#audit axioms Rumoca.CCallPolicy.check_rank_correct
#audit axioms Rumoca.CCallPolicy.check_ranks_correct
#audit axioms Rumoca.CCallPolicy.program_edge_decreases
#audit axioms Rumoca.CCallPolicy.program_no_cycle
#audit axioms Rumoca.CCallPolicy.kernel_no_call
#audit axioms Rumoca.CCallPolicy.function_inventory_ready
#audit axioms Rumoca.CCallPolicy.resolved_named_edge

#audit axioms Rumoca.CCallDepth.Frames.depth_bound
#audit axioms Rumoca.CCallDepth.Frames.weaken
#audit axioms Rumoca.CCallDepth.definition_ready
#audit axioms Rumoca.CCallDepth.enter_ready
#audit axioms Rumoca.CCallDepth.event_ready
#audit axioms Rumoca.CCallDepth.execution_depth_bound
#audit axioms Rumoca.CCallDepth.initial_ready
#audit axioms Rumoca.CCallDepth.internal_ready
#audit axioms Rumoca.CCallDepth.reaches_ready
#audit axioms Rumoca.CCallDepth.ready_depth
#audit axioms Rumoca.CCallDepth.resume_ready
#audit axioms Rumoca.CCallPolicy.entered_internal_edge
#audit axioms Rumoca.CCallPolicy.internal_resolution
#audit axioms Rumoca.CCallPolicy.scheduled_internal_decreases
#audit axioms Rumoca.CCallPolicy.scheduled_internal_edge
#audit axioms Rumoca.CCalls.Events.Linkage.withAddress_foreign
#audit axioms Rumoca.CCalls.Events.Linkage.withExternal_bound
#audit axioms Rumoca.CCalls.Events.Linkage.withExternal_foreign
#audit axioms Rumoca.CCalls.Events.Linkage.withExternal_keeps

#audit axioms Rumoca.CStorage.compare_external
#audit axioms Rumoca.CStorage.exchange_external
#audit axioms Rumoca.CStorage.floor_external
#audit axioms Rumoca.CStorage.length_external
#audit axioms Rumoca.CStorage.rounding_external
#audit axioms Rumoca.CStorage.span_external
#audit axioms Rumoca.CStorage.string_library
#audit axioms Rumoca.CStorage.write_external
#audit axioms Rumoca.CStoreInvariant.concurrent_next
#audit axioms Rumoca.CStoreInvariant.concurrent_reaches
#audit axioms Rumoca.CStoreInvariant.event_next
#audit axioms Rumoca.CStoreInvariant.event_reaches
#audit axioms Rumoca.CStoreInvariant.foreign_change_origin
#audit axioms Rumoca.CStoreInvariant.linked_address
#audit axioms Rumoca.CStoreInvariant.linked_external

#audit axioms Rumoca.CCallSites.checkFunction_correct
#audit axioms Rumoca.CCallSites.checkStatement_correct
#audit axioms Rumoca.CCallSites.concurrent_reaches
#audit axioms Rumoca.CCallSites.concurrent_ready
#audit axioms Rumoca.CCallSites.enter_ready
#audit axioms Rumoca.CCallSites.event_ready
#audit axioms Rumoca.CCallSites.internal_ready
#audit axioms Rumoca.CCallSites.loop_ready_next
#audit axioms Rumoca.CCallSites.named_resolution
#audit axioms Rumoca.CCallSites.operand_permitted
#audit axioms Rumoca.CCallSites.reaches_ready
#audit axioms Rumoca.CCallSites.ready_withHeap
#audit axioms Rumoca.CCallSites.resume_ready
#audit axioms Rumoca.CCalls.Concurrent.external_step_iff
#audit axioms Rumoca.CCalls.Concurrent.internal_step_iff

#audit axioms Rumoca.CAtomicBoolean.Calls.converted_shape
#audit axioms Rumoca.CAtomicBoolean.Calls.exchange_from_arguments
#audit axioms Rumoca.CAtomicBoolean.Calls.write_from_arguments
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.FullReady.atomic_origin
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.FullReady.exit_value
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.FullReady.withHeap
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.Ready.call_origin
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.Ready.exit_value
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.Ready.withHeap
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.call_prefix_bounds
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.full_step_ready
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.full_thread_reaches
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.loop_prefix_bounds
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.step_ready
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.thread_reaches
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.thread_step
#audit axioms Rumoca.CCalls.Concurrent.exit_withHeap
#audit axioms Rumoca.CCalls.Concurrent.external_step_values_iff
#audit axioms Rumoca.CCalls.Concurrent.saved_predicate_step

#audit axioms Rumoca.CAtomicBoolean.exchange_preserves_loaded
#audit axioms Rumoca.CAtomicBoolean.write_preserves_loaded
#audit axioms Rumoca.CCalls.Concurrent.framed_predicate_step
#audit axioms Rumoca.CStoreInvariant.ExceptPreserves.mono
#audit axioms Rumoca.CStoreInvariant.concurrent_classifies
#audit axioms Rumoca.CStoreInvariant.event_classifies
#audit axioms Rumoca.CStoreInvariant.linked_except

#audit axioms Rumoca.CCallSites.Subprogram.event_ready
#audit axioms Rumoca.CCallSites.Subprogram.event_same
#audit axioms Rumoca.CCallSites.Subprogram.functions_admit
#audit axioms Rumoca.CCallSites.Subprogram.internal_same
#audit axioms Rumoca.CCallSites.host_history
#audit axioms Rumoca.CCalls.Events.terminating_path
#audit axioms Rumoca.CCalls.Host.Recording.advance_fresh
#audit axioms Rumoca.CCalls.Host.Recording.advance_origin
#audit axioms Rumoca.CCalls.Host.Recording.aligned_active
#audit axioms Rumoca.CCalls.Host.Recording.callTrace_issued
#audit axioms Rumoca.CCalls.Host.Recording.call_recorded
#audit axioms Rumoca.CCalls.Host.Recording.completion_origin
#audit axioms Rumoca.CCalls.Host.Recording.execution_recorded
#audit axioms Rumoca.CCalls.Host.Recording.history_controls
#audit axioms Rumoca.CCalls.Host.Recording.history_erases
#audit axioms Rumoca.CCalls.Host.Recording.history_invariants
#audit axioms Rumoca.CCalls.Host.Recording.history_issued
#audit axioms Rumoca.CCalls.Host.Recording.history_lift
#audit axioms Rumoca.CCalls.Host.Recording.history_ordered_ids
#audit axioms Rumoca.CCalls.Host.Recording.history_origin
#audit axioms Rumoca.CCalls.Host.Recording.history_unique_ids
#audit axioms Rumoca.CCalls.Host.Recording.initial_aligned
#audit axioms Rumoca.CCalls.Host.Recording.initial_fresh
#audit axioms Rumoca.CCalls.Host.Recording.step_aligned
#audit axioms Rumoca.CCalls.Host.Recording.step_controls
#audit axioms Rumoca.CCalls.Host.call_history
#audit axioms Rumoca.CCalls.Host.complete_iff
#audit axioms Rumoca.CCalls.Host.execute_iff
#audit axioms Rumoca.CCalls.Host.execute_installed
#audit axioms Rumoca.CCalls.Host.execution_history
#audit axioms Rumoca.CCalls.Host.history_threads
#audit axioms Rumoca.CCalls.Host.invoke_iff
#audit axioms Rumoca.CCalls.Host.other_thread
#audit axioms Rumoca.CCalls.Host.step_threads
#audit axioms Rumoca.CCalls.Host.update_twice

#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.ClaimedReady.exit_value
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.ClaimedReady.no_call
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.ClaimedReady.withHeap
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.claimed_interval
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.claimed_step
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.scan_claim_step
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.scan_exchange
#audit axioms Rumoca.CCalls.Concurrent.interval_erases
#audit axioms Rumoca.CCalls.Concurrent.ownTrace_append
#audit axioms Rumoca.CCalls.Concurrent.silent_interval_history
#audit axioms Rumoca.CCalls.Concurrent.silent_saved_step
#audit axioms Rumoca.CCalls.Context.active_of_suspended
#audit axioms Rumoca.CCalls.Context.append_eq_outer
#audit axioms Rumoca.CCalls.Context.appended_heap
#audit axioms Rumoca.CCalls.Context.call_origin
#audit axioms Rumoca.CCalls.Context.depth_append
#audit axioms Rumoca.CCalls.Context.enter_append
#audit axioms Rumoca.CCalls.Context.heap_append
#audit axioms Rumoca.CCalls.Context.internal_append
#audit axioms Rumoca.CCalls.Context.interval_history
#audit axioms Rumoca.CCalls.Context.returned_local
#audit axioms Rumoca.CCalls.Context.saved_step
#audit axioms Rumoca.CCalls.Context.step_append
#audit axioms Rumoca.CCalls.Context.step_unappend

#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.scan_claim_state
#audit axioms Rumoca.CCalls.Context.live_heap
#audit axioms Rumoca.CCalls.Context.step_live
#audit axioms Rumoca.CCalls.Context.suspended_call
#audit axioms Rumoca.CCalls.Context.suspended_heap
#audit axioms Rumoca.CCalls.Context.suspended_step
#audit axioms Rumoca.CCalls.Host.Recording.advance_next
#audit axioms Rumoca.CCalls.Host.Recording.selected_history
#audit axioms Rumoca.CCalls.Host.Recording.selected_step
#audit axioms Rumoca.CMemory.boolean_conversion

#audit axioms Rumoca.CAtomicBoolean.Calls.clear_scheduled
#audit axioms Rumoca.CAtomicBoolean.Calls.exchange_scheduled
#audit axioms Rumoca.CBody.Footprint.heap_free
#audit axioms Rumoca.CBody.Footprint.loop_heap_free
#audit axioms Rumoca.CCalls.Host.Recording.history_replay
#audit axioms Rumoca.CCalls.Host.Recording.history_same_ledger
#audit axioms Rumoca.CLoops.Footprint.assignment_next
#audit axioms Rumoca.CLoops.Footprint.assignment_region
#audit axioms Rumoca.CMemory.Footprint.load_eq
#audit axioms Rumoca.CMemory.Footprint.replace_eq
#audit axioms Rumoca.CMemory.Footprint.store_outside
#audit axioms Rumoca.CMemory.Footprint.store_region
#audit axioms Rumoca.CMemory.Footprint.store_transport

#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.claimed_next
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.claimed_step_heap
#audit axioms Rumoca.CCalls.Host.Recording.current_selected_history
#audit axioms Rumoca.CCalls.Host.Recording.current_selected_step
#audit axioms Rumoca.CCalls.InitializationRegion.CompleteReady.halted
#audit axioms Rumoca.CCalls.InitializationRegion.CompleteReady.withHeap
#audit axioms Rumoca.CCalls.InitializationRegion.CompleteReady.zero_iff_halted
#audit axioms Rumoca.CCalls.InitializationRegion.Ready.exit
#audit axioms Rumoca.CCalls.InitializationRegion.Ready.withHeap
#audit axioms Rumoca.CCalls.InitializationRegion.complete_next_ready
#audit axioms Rumoca.CCalls.InitializationRegion.complete_step_decreases
#audit axioms Rumoca.CCalls.InitializationRegion.complete_step_frame
#audit axioms Rumoca.CCalls.InitializationRegion.complete_step_ready
#audit axioms Rumoca.CCalls.InitializationRegion.next_ready
#audit axioms Rumoca.CCalls.InitializationRegion.remaining_withHeap
#audit axioms Rumoca.CCalls.InitializationRegion.step_ready

#audit axioms Rumoca.CCalls.VoidReturn.Ready.halted_value
#audit axioms Rumoca.CCalls.VoidReturn.Ready.withHeap
#audit axioms Rumoca.CCalls.VoidReturn.Ready.zero_iff_halted
#audit axioms Rumoca.CCalls.VoidReturn.history_ready
#audit axioms Rumoca.CCalls.VoidReturn.next_ready
#audit axioms Rumoca.CCalls.VoidReturn.observed_void
#audit axioms Rumoca.CCalls.VoidReturn.step_ready
#audit axioms Rumoca.CStoreInvariant.host_history
#audit axioms Rumoca.CStoreInvariant.host_next
#audit axioms Rumoca.CStoreInvariant.recorded_history

#audit axioms Rumoca.CCalls.Host.Recording.current_footprint_history
#audit axioms Rumoca.CCalls.Host.Recording.current_footprint_step

#audit axioms Rumoca.CCalls.Host.Recording.advance_unique
#audit axioms Rumoca.CCalls.Host.Recording.history_unique
#audit axioms Rumoca.CCalls.Host.Recording.initial_unique

#audit axioms Rumoca.CCalls.Host.Recording.advance_retained
#audit axioms Rumoca.CCalls.Host.Recording.history_retained
#audit axioms Rumoca.CWriteFootprint.concurrent_region
#audit axioms Rumoca.CWriteFootprint.enter_frame
#audit axioms Rumoca.CWriteFootprint.event_region
#audit axioms Rumoca.CWriteFootprint.internal_frame
#audit axioms Rumoca.CWriteFootprint.internal_region
#audit axioms Rumoca.CWriteFootprint.loop_frame
#audit axioms Rumoca.CWriteFootprint.resume_frame
#audit axioms Rumoca.CWriteFootprint.store_outside
