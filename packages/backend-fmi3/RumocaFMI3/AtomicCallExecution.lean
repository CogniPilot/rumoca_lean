import RumocaC.AtomicArguments
import RumocaC.ConcurrentSteps
import RumocaFMI3.AtomicCallRuntime

/-! Typed atomic operation effects from generated call values and actual scheduler execution. -/
namespace Rumoca.FMI3.AtomicCallPolicy
open CTree CMemory CCalls CCalls.Events
variable [interface : CInterface] {E : Type}

/-- Combine a derived call-value policy with actual conversion and execution.
The selected address comes from the actual atomic operation. Membership in the
pool and the invocation's lease are still separate obligations. -/
theorem exchange_scheduled (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (bound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (values : ∃ object, args = [object, CAtomicBoolean.value true])
    (selected : before.threads thread = some (.calling "atomic_exchange" args savedHeap stack))
    (step : Concurrent.Step program before thread events after) :
    ∃ address observed,
      CAtomicBoolean.exchange before.heap address true = some (observed, after.heap) ∧
      events = [tag (.exchange address observed true)] ∧
      after.threads thread = some (Concurrent.control
        (.returning (CAtomicBoolean.value observed) after.heap stack)) := by
  obtain ⟨object, rfl⟩ := values
  obtain ⟨values, result, heap, converted, executed, rfl⟩ :=
    (Concurrent.external_step_values_iff selected rfl bound).mp step
  obtain ⟨address, observed, _, operation, trace, rfl⟩ :=
    CAtomicBoolean.Calls.exchange_from_arguments tag boolean pointer converted executed
  exact ⟨address, observed, operation, trace, by simp [Concurrent.update]⟩

theorem release_scheduled (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (bound : program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag))
    (values : ∃ object, args = [object, CAtomicBoolean.value false])
    (selected : before.threads thread = some (.calling "atomic_store" args savedHeap stack))
    (step : Concurrent.Step program before thread events after) :
    ∃ address,
      CAtomicBoolean.write before.heap address false = some after.heap ∧
      events = [tag (.write address false)] ∧
      after.threads thread = some (Concurrent.control (.returning .void after.heap stack)) := by
  obtain ⟨object, rfl⟩ := values
  obtain ⟨values, result, heap, converted, executed, rfl⟩ :=
    (Concurrent.external_step_values_iff selected rfl bound).mp step
  obtain ⟨address, _, operation, trace, rfl⟩ :=
    CAtomicBoolean.Calls.write_from_arguments tag boolean pointer converted executed
  exact ⟨address, operation, trace, by simp [Concurrent.update]⟩

end Rumoca.FMI3.AtomicCallPolicy

namespace Rumoca.FMI3.AtomicCallPolicy
open CTree CMemory CCalls CCalls.Events
variable [interface : CInterface] {E : Type}

/-- Actual operation consequences at reachable atomic call boundaries.
The address is obtained from execution; pool membership and lease authorization
are intentionally separate from this typed operational contract. -/
def OperationalCalls (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (before : Concurrent.State) : Prop :=
  (∀ thread args savedHeap stack events after,
    before.threads thread = some (.calling "atomic_exchange" args savedHeap stack) →
    Concurrent.Step program before thread events after →
    ∃ address observed,
      CAtomicBoolean.exchange before.heap address true = some (observed, after.heap) ∧
      events = [tag (.exchange address observed true)] ∧
      after.threads thread = some (Concurrent.control
        (.returning (CAtomicBoolean.value observed) after.heap stack))) ∧
  (∀ thread args savedHeap stack events after,
    before.threads thread = some (.calling "atomic_store" args savedHeap stack) →
    Concurrent.Step program before thread events after →
    ∃ address,
      CAtomicBoolean.write before.heap address false = some after.heap ∧
      events = [tag (.write address false)] ∧
      after.threads thread = some (Concurrent.control (.returning .void after.heap stack)))

theorem operations_of_values (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (exchangeBound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (releaseBound : program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag))
    (exchangeValues : ∀ thread args heap stack,
      before.threads thread = some (.calling "atomic_exchange" args heap stack) →
      ∃ object, args = [object, CAtomicBoolean.value true])
    (releaseValues : ∀ thread args heap stack,
      before.threads thread = some (.calling "atomic_store" args heap stack) →
      ∃ object, args = [object, CAtomicBoolean.value false]) : OperationalCalls program tag before := by
  constructor
  · intro thread args heap stack events after selected step
    exact exchange_scheduled program tag boolean pointer exchangeBound
      (exchangeValues thread args heap stack selected) selected step
  · intro thread args heap stack events after selected step
    exact release_scheduled program tag boolean pointer releaseBound
      (releaseValues thread args heap stack selected) selected step

end Rumoca.FMI3.AtomicCallPolicy
