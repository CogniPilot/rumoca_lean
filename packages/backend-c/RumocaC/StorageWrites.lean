import RumocaC.StorageRegion
import RumocaC.OutputAssignments

namespace Rumoca.CStorage
open CMemory

/-- A cell update retains the allocated object and its declared permissions.
The payload need not be readable or equal to the previous payload. -/
theorem replace_typed (found : heap address = some old) (replacement : Cell)
    (type : replacement.type = old.type) (writable : replacement.writable = old.writable) :
    Preserves heap (replace heap address replacement) := by
  intro query
  by_cases same : query = address
  · subst query
    simp [replace_at, found, description, type, writable]
  · rw [replace_other _ _ _ _ same]

end Rumoca.CStorage

namespace Rumoca.COutputAssignments
open CMemory

theorem write_storage (writable : Writable heap entry) : CStorage.Preserves heap (write heap entry) := by
  obtain ⟨old, found⟩ := writable
  exact CStorage.replace_typed found _ rfl rfl

/-- Prepared output lists retain object storage even when output addresses
alias. Compatibility of output values is a separate execution obligation. -/
theorem after_storage (writable : ∀ entry ∈ entries, Writable heap entry) :
    CStorage.Preserves heap (after heap entries) := by
  induction entries generalizing heap with
  | nil => exact .refl heap
  | cons entry entries ih =>
    have head := writable entry (by simp)
    exact (write_storage head).trans
      (ih (fun other member => writable_preserved head (writable other (by simp [member]))))

end Rumoca.COutputAssignments
