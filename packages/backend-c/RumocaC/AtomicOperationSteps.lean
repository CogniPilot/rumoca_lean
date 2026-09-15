import RumocaC.AtomicArguments
import RumocaC.ConcurrentCalls

namespace Rumoca.CAtomicBoolean.Calls
open CTree CMemory CCalls
variable [interface : CInterface] {E : Type}

/-- An actual shared clear step determines its nonnull address and complete
heap effect, including calls whose address lies outside a particular pool.
It does not confer release authority on the caller. -/
theorem clear_scheduled (program : Events.Program E) (tag : Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (bound : program.externals "atomic_store" = some (writeExternal tag))
    (shape : ∃ object, args = [object, value false])
    (calling : before.threads thread = some (.calling "atomic_store" args oldHeap stack))
    (step : Concurrent.Step program before thread events after) :
    ∃ address, args = [.pointer (some address), value false] ∧
      write before.heap address false = some after.heap ∧ events = [tag (.write address false)] ∧
      after.threads thread = some (Concurrent.control (.returning .void after.heap stack)) := by
  obtain ⟨object, rfl⟩ := shape
  cases step with
  | run selected executed =>
    cases Option.some.inj (selected.symm.trans calling)
    change Events.Step program (.calling "atomic_store" [object, value false] before.heap stack) events _ at executed
    cases executed with
    | internal moved =>
      rw [Events.external_entry_exclusive program bound] at moved
      contradiction
    | external found converted executed =>
      cases Option.some.inj (found.symm.trans bound)
      obtain ⟨address, object, operation, trace, rfl⟩ := write_from_arguments tag boolean pointer converted executed
      refine ⟨address, by simp [object], operation, trace, ?_⟩
      simp [Concurrent.update, CReadOnly.typedHeap]

end Rumoca.CAtomicBoolean.Calls

namespace Rumoca.CAtomicBoolean.Calls
open CTree CMemory CCalls
variable [interface : CInterface] {E : Type}

/-- Extract the actual atomic operation from the shared C step and the raw
canonical operands. No ownership or successful-vacancy premise is needed. -/
theorem exchange_scheduled (program : Events.Program E) (tag : Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (bound : program.externals "atomic_exchange" = some (exchangeExternal tag boolean))
    (calling : before.threads thread = some
      (.calling "atomic_exchange" [.pointer (some address), value true] oldHeap stack))
    (step : Concurrent.Step program before thread events after) :
    ∃ busy, exchange before.heap address true = some (busy, after.heap) ∧
      events = [tag (.exchange address busy true)] := by
  cases step with
  | run selected executed =>
    cases Option.some.inj (selected.symm.trans calling)
    change Events.Step program
      (.calling "atomic_exchange" [.pointer (some address), value true] before.heap stack) events _ at executed
    cases executed with
    | internal moved =>
      rw [Events.external_entry_exclusive program bound] at moved
      contradiction
    | external found converted executed =>
      cases Option.some.inj (found.symm.trans bound)
      obtain ⟨target, busy, same, operation, trace, rfl⟩ :=
        exchange_from_arguments tag boolean pointer converted executed
      cases Option.some.inj (Value.pointer.inj same)
      exact ⟨busy, operation, trace⟩

end Rumoca.CAtomicBoolean.Calls
