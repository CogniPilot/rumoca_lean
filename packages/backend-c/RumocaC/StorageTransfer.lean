import RumocaC.Storage

/-! Transport object premises through executions which preserve the existing
cell domain, declared types and permissions. -/
namespace Rumoca.CStorage
open CMemory

/-- Existing cells retain their type and permissions; only their payload may
change. This transports writable-object premises through reservation calls. -/
theorem Preserves.cell {cell : Cell} (preserved : Preserves before after) (found : before p = some cell) :
    ∃ value, after p = some { cell with value } := by
  have same := preserved p
  rw [found] at same
  cases current : after p with
  | none => simp [current, description] at same
  | some next =>
    obtain ⟨kind, writable⟩ : next.type = cell.type ∧ next.writable = cell.writable := by
      simpa [current, description] using same
    exact ⟨next.value, by cases next; cases cell; simp_all⟩

end Rumoca.CStorage
