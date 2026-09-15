import RumocaFMI3.ConcurrentSlotHistories

/-! Derive the enabled atomic release and its annotation from a current lease and actual call. -/
noncomputable section
namespace Rumoca.FMI3.ConcurrentSlots
open CTree CMemory CCalls CAtomicBoolean
variable [interface : CInterface] {capacity : Nat}

/-- A release call with a derived slot address and the current lease has an
enabled unique atomic step. Argument conversion and the ownership annotation
are constructed; a lease remains an explicit legal-history precondition. -/
theorem release_for_slot (program : Events.Program E) (tag : Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (bound : program.externals "atomic_store" = some (Calls.writeExternal tag))
    (calling : before.threads thread = some (.calling "atomic_store"
      [.pointer (some (AtomicSlots.address block slot)), value false] savedHeap stack))
    (represented : SlotOwners.Represents block before.heap owners)
    (owned : owners (slot : Fin capacity) = some lease) :
    ∃ after : Concurrent.State,
      (∀ effects target, Concurrent.Step program before thread effects target ↔
        effects = [tag (.write (AtomicSlots.address block slot) false)] ∧ target = after) ∧
      SlotOwners.release owners slot lease = some (SlotOwners.update owners slot none) ∧
      SlotOwners.Represents block after.heap (SlotOwners.update owners slot none) ∧
      ScheduledStep program block ⟨before, owners⟩
        [⟨thread, [tag (.write (AtomicSlots.address block slot) false)], some (.release slot lease)⟩]
        ⟨after, SlotOwners.update owners slot none⟩ ∧
      after.threads thread = some (Concurrent.control (.returning .void after.heap stack)) ∧
      (∀ other, other ≠ thread → after.threads other = before.threads other) := by
  have converted := Calls.arguments_converted boolean pointer (AtomicSlots.address block slot) false
  obtain ⟨after, next, released, memory, returned, others, unique⟩ :=
    release_scheduled program tag bound calling rfl converted represented owned
  have fixed := (SlotOwners.release_iff.mp released).2
  subst next
  exact ⟨after, unique, released, memory,
    .release calling rfl converted owned ((unique _ _).mpr ⟨rfl, rfl⟩), returned, others⟩

end Rumoca.FMI3.ConcurrentSlots
