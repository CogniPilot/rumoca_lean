import RumocaC.ConcurrentSteps
import RumocaC.AtomicCalls
import RumocaFMI3.SlotOwners

/-! Actual atomic scheduler calls refine independent slot leases; complete factory classification and native atomic correspondence remain separate. -/
noncomputable section
namespace Rumoca.FMI3.ConcurrentSlots
open CTree CMemory CCalls CAtomicBoolean
variable {capacity : Nat} {owners : SlotOwners.State capacity} {slot : Fin capacity}

/-- A failed claim leaves the current lease untouched; a successful claim
uses the existing independent reservation operation. Lease IDs are ghost
identifiers, not native thread IDs or extra FMI arguments. -/
def Claim (before : SlotOwners.State capacity) (slot : Fin capacity) (lease : Nat)
    (busy : Bool) (after : SlotOwners.State capacity) : Prop :=
  if busy then before slot ≠ none ∧ after = before
  else SlotOwners.reserve before slot lease = some after

theorem claim_busy (claim : Claim before slot lease true after) :
    after = before ∧ before slot ≠ none := ⟨claim.2, claim.1⟩

theorem claim_success (claim : Claim before slot lease false after) :
    before slot = none ∧ after slot = some lease ∧
      ∀ other, SlotOwners.reserve after slot other = none :=
  ⟨(SlotOwners.reserve_iff.mp claim).1, SlotOwners.reserved_owner claim,
    SlotOwners.reserved_excludes claim⟩

/-- Valid represented flag memory supplies an actual atomic operation and its
exact ghost transition. It does not assume successful reservation. -/
theorem reserve_operation (represented : SlotOwners.Represents block before owners)
    (slot : Fin capacity) (lease : Nat) :
    ∃ heap next,
      exchange before (AtomicSlots.address block slot) true =
        some ((SlotOwners.occupied owners) slot, heap) ∧
      Claim owners slot lease ((SlotOwners.occupied owners) slot) next ∧
      SlotOwners.Represents block heap next := by
  obtain ⟨heap, operation, _, _, _⟩ := AtomicSlots.exchange_exists represented slot true
  cases busy : (SlotOwners.occupied owners) slot with
  | false =>
    have step : exchange before (AtomicSlots.address block slot) true = some (false, heap) := by
      simpa only [busy] using operation
    obtain ⟨reserved, next⟩ := SlotOwners.exchange_reserves represented step lease
    exact ⟨heap, _, step, reserved, next⟩
  | true =>
    have step : exchange before (AtomicSlots.address block slot) true = some (true, heap) := by
      simpa only [busy] using operation
    have occupied : owners slot ≠ none := by
      intro vacant
      simp [SlotOwners.occupied, vacant] at busy
    exact ⟨heap, owners, step, ⟨occupied, rfl⟩,
      (SlotOwners.exchange_busy represented step).2⟩

variable [interface : CInterface]

/-- The selected scheduler step both exists and has exactly the specified
reservation result. Only that thread's control is changed. This is an atomic
call boundary, not yet a complete concurrent factory invocation theorem. -/
theorem reserve_scheduled (program : Events.Program E) (tag : Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (bound : program.externals "atomic_exchange" = some (Calls.exchangeExternal tag boolean))
    (selected : before.threads thread = some saved)
    (atCall : Concurrent.withHeap saved before.heap =
      .calling "atomic_exchange" args before.heap stack)
    (converted : Events.convertedArguments Calls.exchangeSignature.parameters args =
      some [.pointer (some (AtomicSlots.address block slot)), value true])
    (represented : SlotOwners.Represents block before.heap owners) (lease : Nat) :
    ∃ after : Concurrent.State, ∃ next : SlotOwners.State capacity,
      Claim owners slot lease ((SlotOwners.occupied owners) slot) next ∧
      SlotOwners.Represents block after.heap next ∧
      after.threads thread = some (Concurrent.control
        (.returning (value ((SlotOwners.occupied owners) slot)) after.heap stack)) ∧
      (∀ other, other ≠ thread → after.threads other = before.threads other) ∧
      ∀ events target, Concurrent.Step program before thread events target ↔
        events = [tag (.exchange (AtomicSlots.address block slot) ((SlotOwners.occupied owners) slot) true)] ∧
        target = after := by
  obtain ⟨heap, next, operation, claim, represented'⟩ := reserve_operation represented slot lease
  let after : Concurrent.State := ⟨heap, Concurrent.update before.threads thread
    (.returning (value ((SlotOwners.occupied owners) slot)) heap stack)⟩
  refine ⟨after, next, claim, represented', by simp [after, Concurrent.update], ?_, ?_⟩
  · intro other different
    simp [after, Concurrent.update, different]
  · intro events target
    rw [Concurrent.external_step_iff selected atCall bound converted]
    constructor
    · rintro ⟨result, finalHeap, executed, rfl⟩
      obtain ⟨same, rfl, rfl⟩ := Calls.exchange_unique tag boolean operation executed
      exact ⟨same, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨_, heap, Calls.exchange_executes tag boolean operation, rfl⟩

/-- Release needs the current ghost lease. It updates the current shared
flag heap and cannot change another thread's saved control. -/
theorem release_scheduled (program : Events.Program E) (tag : Calls.Event → E)
    (bound : program.externals "atomic_store" = some (Calls.writeExternal tag))
    (selected : before.threads thread = some saved)
    (atCall : Concurrent.withHeap saved before.heap =
      .calling "atomic_store" args before.heap stack)
    (converted : Events.convertedArguments Calls.writeSignature.parameters args =
      some [.pointer (some (AtomicSlots.address block slot)), value false])
    (represented : SlotOwners.Represents block before.heap owners)
    (owned : owners slot = some lease) :
    ∃ after : Concurrent.State, ∃ next : SlotOwners.State capacity,
      SlotOwners.release owners slot lease = some next ∧
      SlotOwners.Represents block after.heap next ∧
      after.threads thread = some (Concurrent.control (.returning .void after.heap stack)) ∧
      (∀ other, other ≠ thread → after.threads other = before.threads other) ∧
      ∀ events target, Concurrent.Step program before thread events target ↔
        events = [tag (.write (AtomicSlots.address block slot) false)] ∧ target = after := by
  obtain ⟨heap, operation, _, _, _⟩ := AtomicSlots.exchange_exists represented slot false
  have written := write_as_exchange.mpr ⟨_, operation⟩
  obtain ⟨released, represented'⟩ := SlotOwners.write_releases represented owned written
  let after : Concurrent.State := ⟨heap, Concurrent.update before.threads thread (.returning .void heap stack)⟩
  refine ⟨after, _, released, represented', by simp [after, Concurrent.update], ?_, ?_⟩
  · intro other different
    simp [after, Concurrent.update, different]
  · intro events target
    rw [Concurrent.external_step_iff selected atCall bound converted]
    constructor
    · rintro ⟨result, finalHeap, executed, rfl⟩
      obtain ⟨same, rfl, rfl⟩ := Calls.write_unique tag written executed
      exact ⟨same, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨_, heap, Calls.write_executes tag written, rfl⟩

end Rumoca.FMI3.ConcurrentSlots
