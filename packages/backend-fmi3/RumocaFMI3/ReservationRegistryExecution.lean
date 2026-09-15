import RumocaFMI3.ReservationRegistry
import RumocaC.AtomicOperationSteps
import RumocaC.InvocationLedger
import RumocaFMI3.AtomicFlagFrame

noncomputable section
namespace Rumoca.FMI3.ReservationRegistry
open CTree CMemory CCalls
variable {capacity : Nat}

/-- Compute the reservation effect from a selected C call and its recorded
invocation. The effect log is deliberately not decoded: event tags need not
be injective. This registry is proof-side data, not allocated C storage. -/
def callUpdate (owners : SlotOwners.State capacity) (block : Nat)
    (ledger : Host.Recording.Ledger) (thread : Nat) (name : String) (args : List Value) :
    SlotOwners.State capacity :=
  if name = "atomic_exchange" then
    match args with
    | [.pointer (some address), .integer 1] =>
      match slotAt block capacity address, ledger.active thread with
      | some slot, some call => ConcurrentSlots.claimOwners owners slot call.serial
      | _, _ => owners
    | _ => owners
  else if name = "atomic_store" then
    match args with
    | [.pointer (some address), .integer 0] => clearAt owners block address
    | _ => owners
  else owners

def executeUpdate (owners : SlotOwners.State capacity) (block : Nat)
    (state : Host.Recording.State) (thread : Nat) : SlotOwners.State capacity :=
  match state.runtime.threads thread with
  | some (.calling name args _ _) => callUpdate owners block state.ledger thread name args
  | _ => owners

def AtCall (state : Concurrent.State) (thread : Nat) (name : String) : Prop :=
  ∃ args heap stack, state.threads thread = some (.calling name args heap stack)

theorem executeUpdate_ordinary (owners : SlotOwners.State capacity)
    (exchange : ¬ AtCall state.runtime thread "atomic_exchange")
    (clear : ¬ AtCall state.runtime thread "atomic_store") :
    executeUpdate owners block state thread = owners := by
  unfold executeUpdate
  split
  next name args heap stack found =>
    have nex : name ≠ "atomic_exchange" := by
      intro same; subst name; exact exchange ⟨args, heap, stack, found⟩
    have nclear : name ≠ "atomic_store" := by
      intro same; subst name; exact clear ⟨args, heap, stack, found⟩
    simp [callUpdate, nex, nclear]
  next => rfl

/-- Control/operand facts obtained from the generated program's reachable
histories. No next heap, atomic observation or owner is supplied here. -/
structure Ready (block capacity : Nat) (state : Host.Recording.State) : Prop where
  exchange : ∀ thread args heap stack,
    state.runtime.threads thread = some (.calling "atomic_exchange" args heap stack) →
    ∃ slot : Fin capacity, ∃ call,
      args = [.pointer (some (AtomicSlots.address block slot)), CAtomicBoolean.value true] ∧
      state.ledger.active thread = some call
  clear : ∀ thread args heap stack,
    state.runtime.threads thread = some (.calling "atomic_store" args heap stack) →
    ∃ object, args = [object, CAtomicBoolean.value false]

variable [interface : CInterface] {E : Type}

theorem execute_represents (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (exchangeBound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (clearBound : program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag))
    (foreign : CStoreInvariant.ExceptPreserves CAtomicBoolean.Preserves AtomicFlagFrame.AtomicRoutine program)
    {owners : SlotOwners.State capacity}
    (ready : Ready block capacity state)
    (represented : SlotOwners.Represents block state.runtime.heap owners)
    (step : Concurrent.Step program state.runtime thread events after) :
    SlotOwners.Represents block after.heap (executeUpdate owners block state thread) := by
  by_cases exchange : AtCall state.runtime thread "atomic_exchange"
  · obtain ⟨args, heap, stack, calling⟩ := exchange
    obtain ⟨slot, call, rfl, active⟩ := ready.exchange thread args heap stack calling
    obtain ⟨busy, operation, _⟩ := CAtomicBoolean.Calls.exchange_scheduled
      program tag boolean pointer exchangeBound calling step
    simpa [executeUpdate, calling, callUpdate, CAtomicBoolean.value, slotAt_address, active] using
      (claim_represents represented operation call.serial).2
  by_cases clear : AtCall state.runtime thread "atomic_store"
  · obtain ⟨args, heap, stack, calling⟩ := clear
    obtain ⟨address, args, operation, _, _⟩ := CAtomicBoolean.Calls.clear_scheduled
      program tag boolean pointer clearBound (ready.clear thread args heap stack calling) calling step
    simpa [executeUpdate, calling, callUpdate, args, CAtomicBoolean.value] using
      clear_represents represented operation
  rw [executeUpdate_ordinary owners exchange clear]
  apply SlotOwners.ordinary_preserves represented
  rcases CStoreInvariant.concurrent_classifies CAtomicBoolean.ordinary_stable foreign step with
    frame | ⟨saved, name, args, stack, selected, atCall, atomic⟩
  · exact frame
  · cases saved with
    | calling name' args' heap stack' =>
      cases atCall
      rcases atomic with rfl | rfl
      · exact False.elim (exchange ⟨_, _, _, selected⟩)
      · exact False.elim (clear ⟨_, _, _, selected⟩)
    | body state => cases state <;> contradiction
    | kernel | returning | halted => contradiction

end Rumoca.FMI3.ReservationRegistry
