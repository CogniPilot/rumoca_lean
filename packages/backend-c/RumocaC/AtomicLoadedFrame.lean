import RumocaC.AtomicBoolean

/-! Atomic updates preserve successfully loaded ordinary cells, without extra alias premises. -/
namespace Rumoca.CAtomicBoolean
open CMemory

/-- An atomic update cannot alias an ordinary cell that was successfully
loaded. The separation follows from the modeled cell types, not an additional
address inequality supplied by the caller. -/
theorem exchange_preserves_loaded
    (operation : exchange before p desired = some (observed, after))
    (read : load before q = some datum) : after q = before q := by
  apply exchange_frame operation
  intro same
  subst q
  rw [ordinary_load_unsupported (exchange_iff.mp operation).1] at read
  contradiction

theorem write_preserves_loaded
    (operation : write before p desired = some after)
    (read : load before q = some datum) : after q = before q := by
  apply write_frame operation
  intro same
  subst q
  obtain ⟨observed, found⟩ := (write_iff.mp operation).1
  rw [ordinary_load_unsupported found] at read
  contradiction

end Rumoca.CAtomicBoolean
