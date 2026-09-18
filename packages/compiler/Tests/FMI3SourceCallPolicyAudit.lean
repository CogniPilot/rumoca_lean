import Rumoca.FMI3ControlledInitialization
import Rumoca.FMI3RetainedInitialization
import Rumoca.FMI3ResourceHistories
import Rumoca.FMI3InstanceAuthority
import Rumoca.FMI3PublicationHistories
import Rumoca.FMI3StaticInitializationHistories
import Rumoca.FMI3InitializationHistories
import Rumoca.FMI3ReservationHistories
import Rumoca.FMI3FactoryClaims
import Rumoca.FMI3ScanClaims
import Rumoca.FMI3FactorySuffix
import Rumoca.FMI3SubcallDomains
import Rumoca.FMI3HostCalls
import Rumoca.FMI3InitialRecorded
import Rumoca.FMI3ReservationOrigins
import Rumoca.FMI3AtomicFlagFrame
import Rumoca.FMI3ReleaseBounds
import Rumoca.FMI3AtomicOperations
import Rumoca.FMI3ReservationBounds
import Rumoca.FMI3ConcurrentSlots
import Rumoca.FMI3AtomicCalls
import Rumoca.FMI3RuntimeStorage
import Rumoca.FMI3StateSetterPolicy
import Rumoca.FMI3RuntimeLinkage
import Rumoca.FMI3CallPolicy
import ProofAudit.Audit

/-! Independently cached formal audits for the call policy; no example-based tests. -/

#audit axioms Rumoca.FMI3.CallPolicy.actual_adapter_policy
#audit axioms Rumoca.FMI3.CallPolicy.source_program_policy

#audit axioms Rumoca.FMI3.CallPolicy.unit_no_heap
#audit axioms Rumoca.FMI3.CallPolicy.unit_acyclic

#audit axioms Rumoca.FMI3.RuntimeLinkage.source_logged_environment

#audit axioms Rumoca.FMI3.RuntimeStorage.source_resource_environment
#audit axioms Rumoca.FMI3.StateSetterPolicy.source_permission

#audit axioms Rumoca.FMI3.AtomicCallPolicy.source_atomic_calls
#audit axioms Rumoca.FMI3.ConcurrentSlots.source_slot_histories

#audit axioms Rumoca.FMI3.AtomicCallPolicy.source_atomic_operations
#audit axioms Rumoca.FMI3.ConcurrentSlots.source_reservation_bounds

#audit axioms Rumoca.FMI3.AtomicFlagFrame.source_flag_frames
#audit axioms Rumoca.FMI3.ConcurrentSlots.source_release_bounds

#audit axioms Rumoca.FMI3.AtomicCallPolicy.source_host_calls
#audit axioms Rumoca.FMI3.ReservationOrigin.source_reservation_origins
#audit axioms Rumoca.FMI3.StaticRuntime.source_recorded_creation

#audit axioms Rumoca.FMI3.ConcurrentSlots.source_scan_claims
#audit axioms Rumoca.FMI3.ReservationOrigin.source_factory_suffix
#audit axioms Rumoca.FMI3.ReservationOrigin.source_subcall_domains

#audit axioms Rumoca.FMI3.ConcurrentSlots.source_factory_claims

#audit axioms Rumoca.FMI3.ReservationRegistry.source_reservation_histories

#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.source_factory_initializations

#audit axioms Rumoca.FMI3.PublicationRegistry.source_publication_histories
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.source_creation_histories
#audit axioms Rumoca.FMI3.StaticFactory.ClaimInitialization.source_static_factory_initializations

#audit axioms Rumoca.FMI3.InstanceAuthority.source_authorized_release

#audit axioms Rumoca.FMI3.InstanceAuthority.source_resource_histories

#audit axioms Rumoca.FMI3.InstanceAuthority.source_retained_initialization

#audit axioms Rumoca.FMI3.InstanceAuthority.source_controlled_initialization
