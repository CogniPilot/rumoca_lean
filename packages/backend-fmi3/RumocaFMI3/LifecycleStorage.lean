import RumocaFMI3.LifecycleBodies
import RumocaC.StorageTransfer
import RumocaC.AtomicFrame

namespace Rumoca.FMI3.LifecycleBodies
open CMemory

theorem write_store (heap : Heap) (p : Address) (old : Option Value) (mode : Mode)
    (stored : heap (p.member "mode") = some ⟨.int32, true, old⟩) :
    store heap (p.member "mode") (.integer mode.code) = some (writeMode heap p mode) := by
  cases mode <;> simp [store, stored, convert, writeMode, Mode.code]

theorem write_storage (heap : Heap) (p : Address) (old : Option Value) (mode : Mode)
    (stored : heap (p.member "mode") = some ⟨.int32, true, old⟩) :
    CStorage.Preserves heap (writeMode heap p mode) ∧
    CReadOnly.Preserves heap (writeMode heap p mode) ∧
    CAtomicBoolean.Preserves heap (writeMode heap p mode) := by
  have run := write_store heap p old mode stored
  exact ⟨CStorage.store_preserves run, CReadOnly.store_preserves run, CAtomicBoolean.ordinary_store_preserves run⟩

end Rumoca.FMI3.LifecycleBodies
