import RumocaFMI3.ConcurrentSlotHistories

/-! Derive reservation ownership annotations from bounded actual scheduler calls. -/
namespace Rumoca.FMI3.ConcurrentSlots
open CTree CMemory CCalls CAtomicBoolean
variable [interface : CInterface] {capacity : Nat}

/-- A bounded actual reservation call has an enabled, unique atomic step and
its ownership annotation is derived. The caller supplies represented shared
flags, but no converted arguments, successful scan, or next-state annotation. -/
theorem bounded_reservation_claim (program : Events.Program E) (tag : Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (bound : program.externals "atomic_exchange" = some (Calls.exchangeExternal tag boolean))
    (bounded : ∀ args heap stack,
      before.threads thread = some (.calling "atomic_exchange" args heap stack) →
      ∃ slot : Fin capacity,
        args = [.pointer (some (AtomicSlots.address block slot)), value true])
    (calling : before.threads thread = some (.calling "atomic_exchange" args savedHeap stack))
    (represented : SlotOwners.Represents block before.heap owners) (lease : Nat) :
    ∃ slot : Fin capacity, ∃ after : Concurrent.State,
      let busy := (SlotOwners.occupied owners) slot
      let next := claimOwners owners slot lease
      (∀ effects target, Concurrent.Step program before thread effects target ↔
        effects = [tag (.exchange (AtomicSlots.address block slot) busy true)] ∧ target = after) ∧
      Claim owners slot lease busy next ∧
      SlotOwners.Represents block after.heap next ∧
      ScheduledStep program block ⟨before, owners⟩
        [⟨thread, [tag (.exchange (AtomicSlots.address block slot) busy true)], some (.claim slot lease busy)⟩]
        ⟨after, next⟩ ∧
      after.threads thread = some (Concurrent.control (.returning (value busy) after.heap stack)) ∧
      (∀ other, other ≠ thread → after.threads other = before.threads other) := by
  obtain ⟨slot, rfl⟩ := bounded args savedHeap stack calling
  have converted := Calls.arguments_converted boolean pointer (AtomicSlots.address block slot) true
  obtain ⟨after, next, claimed, memory, returned, others, unique⟩ :=
    reserve_scheduled program tag boolean bound calling rfl converted represented lease
  have target := claimed.target
  subst next
  exact ⟨slot, after, unique, claimed, memory,
    .claim calling rfl converted ((unique _ _).mpr ⟨rfl, rfl⟩), returned, others⟩

end Rumoca.FMI3.ConcurrentSlots
