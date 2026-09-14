import RumocaC.StorageTransfer
import RumocaC.ArrayStore

/-! Typed storage preservation over a caller-selected region. Foreign effects
may change their private storage; the protected region retains its cell domain,
types and permissions. Scalar cells and indexed buffers use the same relation. -/
namespace Rumoca.CStorage
open CMemory

def PreservesOn (region : Address → Prop) (before after : Heap) : Prop :=
  ∀ p, region p → description (after p) = description (before p)

theorem PreservesOn.refl (region : Address → Prop) (heap : Heap) : PreservesOn region heap heap :=
  fun _ _ => rfl

theorem PreservesOn.trans (first : PreservesOn region before middle) (second : PreservesOn region middle after) :
    PreservesOn region before after := fun p inside => (second p inside).trans (first p inside)

theorem Preserves.on (preserved : Preserves before after) (region : Address → Prop) :
    PreservesOn region before after := fun p _ => preserved p

theorem PreservesOn.of_frame (frame : ∀ p, region p → after p = before p) : PreservesOn region before after :=
  fun p inside => congrArg description (frame p inside)

theorem PreservesOn.cell (preserved : PreservesOn region before after) (inside : region p)
    {cell : Cell} (found : before p = some cell) : ∃ value, after p = some { cell with value } := by
  have same := preserved p inside
  rw [found] at same
  cases current : after p with
  | none => simp [current, description] at same
  | some next =>
    obtain ⟨kind, writable⟩ : next.type = cell.type ∧ next.writable = cell.writable := by
      simpa [current, description] using same
    exact ⟨next.value, by cases next; cases cell; simp_all⟩

theorem PreservesOn.array (preserved : PreservesOn region before after)
    (base : Address) (type : CType) (count : Nat) (stored : ArrayStore.Writable before base type count)
    (guarded : ∀ i < count, region (base.index i)) : ArrayStore.Writable after base type count := by
  intro i inside
  obtain ⟨old, cell⟩ := stored i inside
  exact preserved.cell (guarded i inside) cell

end Rumoca.CStorage
