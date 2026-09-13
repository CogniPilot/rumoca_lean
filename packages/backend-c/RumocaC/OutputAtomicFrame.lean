import RumocaC.OutputAssignments
import RumocaC.AtomicFrame

noncomputable section
namespace Rumoca.CAtomicBoolean
open CMemory

/-- Replacing a represented non-atomic cell cannot alter any existing atomic
reservation. Typed storage excludes aliasing with an atomic cell. -/
theorem replace_nonatomic (found : before address = some old)
    (nonatomic : old.type ≠ .atomicBoolean) (replacement : Cell) :
    Preserves before (replace before address replacement) := by
  intro query busy atomic
  have outside : query ≠ address := by
    intro same
    rw [same] at atomic
    have cells := Option.some.inj (found.symm.trans atomic)
    exact nonatomic (congrArg Cell.type cells)
  exact (replace_other _ _ _ _ outside).trans atomic

end Rumoca.CAtomicBoolean

namespace Rumoca.COutputAssignments
open CMemory

theorem write_atomic (writable : Writable heap entry) (nonatomic : entry.type ≠ .atomicBoolean) :
    CAtomicBoolean.Preserves heap (write heap entry) := by
  obtain ⟨old, found⟩ := writable
  exact CAtomicBoolean.replace_nonatomic found nonatomic _

/-- Atomic preservation for arbitrary prepared output lists, with aliases
allowed. This is an invariant of ordinary writes, not an extra host premise. -/
theorem after_atomic (writable : ∀ entry ∈ entries, Writable heap entry)
    (nonatomic : ∀ entry ∈ entries, entry.type ≠ .atomicBoolean) :
    CAtomicBoolean.Preserves heap (after heap entries) := by
  induction entries generalizing heap with
  | nil => exact .refl heap
  | cons entry entries ih =>
    have head := writable entry (by simp)
    exact (write_atomic head (nonatomic entry (by simp))).trans
      (ih (fun other member => writable_preserved head (writable other (by simp [member])))
        (fun other member => nonatomic other (by simp [member])))

end Rumoca.COutputAssignments
