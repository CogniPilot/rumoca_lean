import RumocaFMI3.ReservationOriginPolicy
import RumocaFMI3.RuntimeLinkage
import RumocaC.InvocationOrigins
import RumocaC.InvocationControl

namespace Rumoca.FMI3.ReservationOrigin
open CTree CMemory CCalls CCalls.Events CCallSites RuntimeLinkage

theorem entry_allowed (ranked : CallPolicy.functionRank name = some 2) (notFactory : ¬ factory name) :
    allowed name = true := by
  cases selected : allowed name with
  | true => rfl
  | false =>
    rcases (excluded name).mp selected with isFactory | rfl | rfl
    · exact False.elim (notFactory isFactory)
    · have helper : CallPolicy.functionRank "rumoca_reserve_slot" = some 1 := by decide +kernel
      rw [helper] at ranked
      cases ranked
    · have absent : CallPolicy.functionRank "atomic_exchange" = none := by decide +kernel
      rw [absent] at ranked
      contradiction

def RootReady (call : Host.Recording.Invocation) (state : Typed.State) : Prop :=
  ¬ factory call.name → Ready Permitted (fun name _ => allowed name = true) state

variable [interface : CInterface]

omit interface in
theorem root_heap (ready : RootReady call state) (heap : Heap) : RootReady call (Concurrent.withHeap state heap) :=
  fun notFactory => (ready_withHeap state heap).mpr (ready notFactory)

omit interface in
theorem root_excluded (ready : RootReady call (.calling name args heap stack))
    (outside : allowed name = false) : factory call.name := by
  by_contra notFactory
  have permitted : allowed name = true := (ready notFactory).1
  rw [outside] at permitted
  contradiction

theorem logged_named_only (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName))
    (outside : allowed name = false) :
    NamedOnly (logged model sigs covered tag boolean size integer double observed range logger effect) name := by
  intro address found
  change (if address = logger then some hostName else none) = some name at found
  split at found
  · cases Option.some.inj found
    have permitted : allowed hostName = true := by decide +kernel
    rw [permitted] at outside
    contradiction
  · contradiction

/-- The invariant follows the exact recorded public invocation through actual
calls, returns and shared-heap interleavings; no enclosing-factory annotation
is supplied at reservation. -/
theorem logged_controls (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName))
    (domain : Concurrent.State → Nat → Signature → List Value → Prop)
    (memory : Concurrent.State → Nat → Heap → Prop) :
    let program := logged model sigs covered tag boolean size integer double observed range logger effect
    ∀ heap ticks after, Transition.Events.Reaches (Host.Recording.Step program (Host.publicPolicy sigs domain memory))
      ⟨⟨heap, fun _ => none⟩, Host.Recording.initial⟩ ticks after → Host.Recording.Controls RootReady after := by
  intro program heap ticks after path
  let policy := Host.publicPolicy sigs domain memory
  have entry : ∀ serial state thread name args, policy.admit state thread name args →
      RootReady ⟨serial, name, args⟩ (.calling name args state.heap .done) := by
    intro serial state thread name args admitted notFactory
    obtain ⟨sig, member, rfl, _⟩ := admitted
    exact ⟨entry_allowed (CallPolicy.covered_ranks covered sig member) notFactory, True.intro⟩
  have idle : Host.Recording.Controls RootReady ⟨⟨heap, fun _ => none⟩, Host.Recording.initial⟩ := by
    intro thread saved call found active
    contradiction
  exact Host.Recording.history_controls program policy RootReady
    (fun _ _ ready heap => root_heap ready heap) entry
    (fun _ _ _ _ ready step notFactory => event_ready model sigs program rfl
      (fun _ outside => logged_named_only model sigs covered tag boolean size integer double observed range logger effect outside)
      (ready notFactory) step) idle path

/-- Every actual raw host history computes the invocation records needed to
identify reservation origins. The helper and exchange cannot come from another
public entry, and the active serial/name/arguments trace back to its actual
earlier invocation. No later-call or owner annotation is an input. -/
theorem logged_host_origins (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName))
    (domain : Concurrent.State → Nat → Signature → List Value → Prop)
    (memory : Concurrent.State → Nat → Heap → Prop) :
    let program := logged model sigs covered tag boolean size integer double observed range logger effect
    ∀ heap trace after, Host.History program (Host.publicPolicy sigs domain memory) ⟨heap, fun _ => none⟩ trace after →
      ∃ ledger ticks, Host.Recording.erase ticks = trace ∧
        Transition.Events.Reaches (Host.Recording.Step program (Host.publicPolicy sigs domain memory))
          ⟨⟨heap, fun _ => none⟩, Host.Recording.initial⟩ ticks ⟨after, ledger⟩ ∧
        (Host.Recording.issued ticks).Nodup ∧
        ∀ thread name args savedHeap stack, after.threads thread = some (.calling name args savedHeap stack) →
          allowed name = false → ∃ call, ledger.active thread = some call ∧ factory call.name ∧
            call.serial < ledger.next ∧ ∃ tick ∈ ticks, Host.Recording.Started thread call tick := by
  intro program heap trace after path
  obtain ⟨ledger, ticks, erased, recorded⟩ := Host.Recording.history_lift program _ path Host.Recording.initial
  have controls := logged_controls model sigs covered tag boolean size integer double observed range logger effect
    domain memory heap ticks ⟨after, ledger⟩ recorded
  obtain ⟨aligned, fresh⟩ := Host.Recording.history_invariants recorded
    (Host.Recording.initial_aligned heap) Host.Recording.initial_fresh
  refine ⟨ledger, ticks, erased, recorded, Host.Recording.history_unique_ids recorded, ?_⟩
  intro thread name args savedHeap stack found outside
  obtain ⟨call, active⟩ := Host.Recording.aligned_active aligned found
  refine ⟨call, active, root_excluded (controls thread _ call found active) outside, fresh thread call active, ?_⟩
  rcases Host.Recording.history_origin recorded active with absent | started
  · contradiction
  · exact started

end Rumoca.FMI3.ReservationOrigin
