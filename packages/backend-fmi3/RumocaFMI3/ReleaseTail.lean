import RumocaC.VoidReturn
import RumocaFMI3.ReleaseInvariant

namespace Rumoca.FMI3.StaticRelease
open CTree CMemory CCalls
variable [interface : CInterface] {E : Type}

/-- Once the real release call has captured its atomic operands, its actual
clear enters a heap-independent return suffix. Neither metadata preservation
nor absence of immediate reuse is needed for this suffix. Authority to perform
the clear remains the separate lease-checked precondition. -/
theorem clear_return_tail (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (bound : program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag))
    (ready : ConcurrentInvariant.Ready p flags slot .done (.calling name args heap later))
    (atomic : name = "atomic_store")
    (step : Events.Step program (.calling name args heap later) events after) :
    CAtomicBoolean.write heap (flags.index slot) false = some (CReadOnly.typedHeap after) ∧
    events = [tag (.write (flags.index slot) false)] ∧
    VoidReturn.Ready (locals p) types after := by
  cases ready with
  | entry => simp [function] at atomic
  | atomic address =>
    cases step with
    | internal next =>
      rw [Events.external_entry_exclusive program bound] at next
      contradiction
    | external found converted executed =>
      cases Option.some.inj (found.symm.trans bound)
      obtain ⟨target, pointerEq, written, trace, rfl⟩ :=
        CAtomicBoolean.Calls.write_from_arguments tag boolean pointer converted executed
      have same : flags.index slot = target := by simpa using pointerEq
      subst target
      exact ⟨written, trace, .resumed _⟩

/-- The actual release suffix remains valid throughout recorded host actions,
including storage reuse by another factory. Its observed completion is void
and cannot modify any cell of the heap then present. -/
theorem return_tail_observed (program : Events.Program E) (policy : Host.Policy)
    (issued : serial < before.ledger.next)
    (selected : before.runtime.threads tracked = some saved)
    (ready : VoidReturn.Ready (locals p) types saved)
    (path : Transition.Events.Reaches (Host.Recording.Step program policy) before ticks after)
    (active : after.ledger.active tracked = some call) (origin : call.serial = serial)
    (completed : Host.Step program policy after.runtime tracked (.complete value) following) :
    value = .void ∧ following.heap = after.runtime.heap := by
  apply VoidReturn.observed_void (env := locals p) (types := types) program policy issued ?_ path active origin completed
  intro original chosen _ _ found
  cases Option.some.inj (found.symm.trans selected)
  exact ready

end Rumoca.FMI3.StaticRelease
