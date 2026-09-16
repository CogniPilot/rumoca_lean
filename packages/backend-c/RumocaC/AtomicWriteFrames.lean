import RumocaC.WriteRegions
import RumocaC.AtomicArguments

namespace Rumoca.CAtomicBoolean.Calls
open CTree CMemory CCalls
variable [interface : CInterface] {E : Type} {region : Set Address}

/-- The bound atomic exchange's frame follows from the real parameter casts
and checked atomic update. It is not a supplied callback frame. -/
theorem exchange_foreign_frame (program : Events.Program E) (tag : Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (bound : program.externals "atomic_exchange" = some (exchangeExternal tag boolean))
    (outside : address ∉ region) :
    CWriteFootprint.ForeignFrame region program
      (.calling "atomic_exchange" [.pointer (some address), value desired] heap stack) := by
  intro fn values events result after found converted executed
  cases Option.some.inj (found.symm.trans bound)
  obtain ⟨selected, observed, pointerEq, operation, _, _⟩ :=
    exchange_from_arguments tag boolean pointer converted executed
  have same : address = selected := Option.some.inj (Value.pointer.inj pointerEq)
  subst selected
  intro query inside
  exact (exchange_frame operation (fun same => outside (same ▸ inside))).symm

/-- Atomic release has the same one-cell exterior frame, including arbitrary
saved caller continuations whose later writes are checked separately. -/
theorem write_foreign_frame (program : Events.Program E) (tag : Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (bound : program.externals "atomic_store" = some (writeExternal tag))
    (outside : address ∉ region) :
    CWriteFootprint.ForeignFrame region program
      (.calling "atomic_store" [.pointer (some address), value desired] heap stack) := by
  intro fn values events result after found converted executed
  cases Option.some.inj (found.symm.trans bound)
  obtain ⟨selected, pointerEq, operation, _, _⟩ :=
    write_from_arguments tag boolean pointer converted executed
  have same : address = selected := Option.some.inj (Value.pointer.inj pointerEq)
  subst selected
  intro query inside
  exact (write_frame operation (fun same => outside (same ▸ inside))).symm

end Rumoca.CAtomicBoolean.Calls
