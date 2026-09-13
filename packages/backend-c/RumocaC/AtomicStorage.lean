import RumocaC.AtomicBoolean
import RumocaC.Storage

/-! Atomic reservation operations preserve the supplied object domain, types,
permissions and read-only cells. These are memory-operation consequences;
native atomic binding, interleavings and complete calls remain separate. -/
namespace Rumoca.CAtomicBoolean
open CMemory

theorem write_as_exchange : write before p next = some after ↔
    ∃ old, exchange before p next = some (old, after) := by
  simp only [write_iff, exchange_iff, exists_and_right]

theorem exchange_storage (step : exchange before p next = some (old, after)) :
    CStorage.Preserves before after := by
  intro q
  by_cases same : q = p
  · subst q
    have spec := exchange_iff.mp step
    rw [spec.2, replace_at, spec.1]
    rfl
  · rw [exchange_frame step same]

theorem exchange_readonly (step : exchange before p next = some (old, after)) :
    CReadOnly.Preserves before after := by
  intro q entry found readonly
  by_cases same : q = p
  · subst q
    rw [(exchange_iff.mp step).1] at found
    cases Option.some.inj found
    simp [cell] at readonly
  · rw [exchange_frame step same, found]

theorem write_storage (step : write before p next = some after) :
    CStorage.Preserves before after := by
  obtain ⟨old, exchanged⟩ := write_as_exchange.mp step
  exact exchange_storage exchanged

theorem write_readonly (step : write before p next = some after) :
    CReadOnly.Preserves before after := by
  obtain ⟨old, exchanged⟩ := write_as_exchange.mp step
  exact exchange_readonly exchanged

/-- Formal starting memory for a separately declared static array. This is
construction of the program's initial state, not runtime allocation. -/
def initial (heap : Heap) (block capacity : Nat) : Heap := fun p =>
  if p.block = block ∧ p.members = [] ∧ p.offset < capacity then some (cell false)
  else heap p

theorem initial_at (heap : Heap) (block capacity : Nat) (i : Fin capacity) :
    initial heap block capacity ⟨block, [], i.val⟩ = some (cell false) := by
  simp [initial, i.isLt]

theorem initial_read (heap : Heap) (block capacity : Nat) (i : Fin capacity) :
    read (initial heap block capacity) ⟨block, [], i.val⟩ = some false :=
  read_iff.mpr (initial_at heap block capacity i)

theorem initial_frame (outside : p.block ≠ block ∨ p.members ≠ [] ∨ capacity ≤ p.offset) :
    initial heap block capacity p = heap p := by
  rcases outside with different | different | beyond <;> simp [initial, *]

theorem initial_readonly (fresh : ∀ p, p.block = block → p.members = [] →
    p.offset < capacity → heap p = none) : CReadOnly.Preserves heap (initial heap block capacity) := by
  intro p entry found readonly
  have outside : p.block ≠ block ∨ p.members ≠ [] ∨ capacity ≤ p.offset := by
    by_contra inside
    simp only [not_or, ne_eq, not_not, Nat.not_le] at inside
    rw [fresh p inside.1 inside.2.1 inside.2.2] at found
    contradiction
  rw [initial_frame outside, found]

end Rumoca.CAtomicBoolean
