import RumocaFMI3.RecordedReservation
import RumocaFMI3.ReservationOriginRuntime

namespace Rumoca.FMI3.ReservationOrigin
open CTree CMemory CCalls CCalls.Events RuntimeLinkage ConcurrentSlots
variable [interface : CInterface] {capacity : Nat}

/-- Actual raw public-call history supplies the factory descriptor. Its fresh
serial becomes the lease in the very next bounded exchange. Bounds and current
flag representation remain explicit until whole factory histories derive them. -/
theorem logged_claim_origins (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName))
    (domain : Concurrent.State → Nat → Signature → List Value → Prop)
    (memory : Concurrent.State → Nat → Heap → Prop) :
    let program := logged model sigs covered tag boolean size integer double observed range logger effect
    let policy := Host.publicPolicy sigs domain memory
    ∀ initialHeap trace before, Host.History program policy ⟨initialHeap, fun _ => none⟩ trace before →
      ∃ ledger ticks, Host.Recording.erase ticks = trace ∧
        Transition.Events.Reaches (Host.Recording.Step program policy)
          ⟨⟨initialHeap, fun _ => none⟩, Host.Recording.initial⟩ ticks ⟨before, ledger⟩ ∧
        (Host.Recording.issued ticks).Nodup ∧
        ∀ (block thread : Nat) (args : List Value) (savedHeap : Heap) (stack : Typed.Continuation),
          before.threads thread = some (.calling "atomic_exchange" args savedHeap stack) →
          (∀ args heap stack, before.threads thread = some (.calling "atomic_exchange" args heap stack) →
            ∃ slot : Fin capacity, args = [.pointer (some (AtomicSlots.address block slot)), CAtomicBoolean.value true]) →
          ∀ owners : SlotOwners.State capacity, SlotOwners.Represents block before.heap owners →
            ∃ call, ledger.active thread = some call ∧ factory call.name ∧ call.serial < ledger.next ∧
              (∃ tick ∈ ticks, Host.Recording.Started thread call tick) ∧
              RecordedClaim program policy tag block before ledger owners thread call := by
  intro program policy initialHeap trace before path
  obtain ⟨ledger, ticks, erased, recorded, unique, origins⟩ :=
    logged_host_origins model sigs covered tag boolean size integer double observed range logger effect
      domain memory initialHeap trace before path
  obtain ⟨_, _, _, _, library, _, _⟩ :=
    logged_contract model sigs covered tag boolean size integer double observed range logger none effect
  refine ⟨ledger, ticks, erased, recorded, unique, ?_⟩
  intro block thread args savedHeap stack calling bounded owners represented
  obtain ⟨call, active, isFactory, fresh, started⟩ :=
    origins thread "atomic_exchange" args savedHeap stack calling (by decide +kernel)
  exact ⟨call, active, isFactory, fresh, started,
    recorded_claim program policy tag boolean pointer (library "atomic_exchange" _ rfl) active bounded calling represented⟩

end Rumoca.FMI3.ReservationOrigin
