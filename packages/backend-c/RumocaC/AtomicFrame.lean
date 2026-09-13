import RumocaC.AtomicBoolean
import RumocaC.StoreInvariant

/-! Ordinary internal execution cannot change the atomic reservation cells.
This complements the atomic operations' frame theorems and permits a shared
slot invariant to survive ordinary work interleaved with reservation calls. -/
namespace Rumoca.CAtomicBoolean
open CMemory

def Preserves (before after : Heap) : Prop :=
  ∀ p busy, before p = some (cell busy) → after p = some (cell busy)

theorem Preserves.refl (heap : Heap) : Preserves heap heap := fun _ _ found => found

theorem Preserves.trans (first : Preserves a b) (second : Preserves b c) : Preserves a c :=
  fun p busy found => second p busy (first p busy found)

theorem ordinary_store_preserves {storedValue : Value}
    (step : store before address storedValue = some after) : Preserves before after := by
  intro p busy found
  by_cases same : p = address
  · subst address
    rw [ordinary_store_unsupported found] at step
    contradiction
  · rw [store_frame _ _ _ _ step _ same, found]

theorem ordinary_stable : CStoreInvariant.Stable Preserves :=
  ⟨Preserves.refl, fun _ _ _ _ step => ordinary_store_preserves step⟩

variable [interface : CInterface]

theorem internal_preserves (program : CCalls.Events.Program E)
    (step : CCalls.Events.internalNext program s = some t) :
    Preserves (CReadOnly.typedHeap s) (CReadOnly.typedHeap t) :=
  CStoreInvariant.internal_next ordinary_stable program step

end Rumoca.CAtomicBoolean
