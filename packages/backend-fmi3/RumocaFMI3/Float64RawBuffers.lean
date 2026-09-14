import RumocaFMI3.Float64Buffers
import RumocaC.StoreRunInvariant
import RumocaC.AtomicFrame

namespace Rumoca.FMI3.Float64Buffers
open CMemory

/-- Raw caller payloads include every IEEE encoding, so rejected non-finite
writes are prepared through the same typed-store semantics as finite inputs. -/
def rawValues (count : Nat) (bits : Nat → BitVec 64) : Fin count → Value :=
  fun i => .float64 (bits i.val)

def prepareRawValues (heap : Heap) (base : Address) (count : Nat) (bits : Nat → BitVec 64) : Heap :=
  ArrayStore.written heap base .float64 (rawValues count bits) count

theorem raw_values_run (heap : Heap) (base : Address) (count : Nat) (bits : Nat → BitVec 64)
    (stored : TensorView.Writable heap base count) :
    ArrayStore.run heap base (rawValues count bits) count = some (prepareRawValues heap base count bits) :=
  ArrayStore.run_written _ _ _ _ _ (by omega) stored (by decide) (fun _ => rfl)

theorem raw_values_read (heap : Heap) (base : Address) (count : Nat) (bits : Nat → BitVec 64)
    (i : Nat) (inside : i < count) :
    load (prepareRawValues heap base count bits) (base.index i) = some (.float64 (bits i)) :=
  ArrayStore.written_reads heap base .float64 (rawValues count bits) (by decide) (fun _ => rfl) ⟨i, inside⟩

theorem raw_values_frame (heap : Heap) (base : Address) (count : Nat) (bits : Nat → BitVec 64)
    (q : Address) (outside : ∀ i < count, q ≠ base.index i) :
    prepareRawValues heap base count bits q = heap q :=
  ArrayStore.frame _ _ _ _ _ q (fun i => outside i.val i.isLt)

theorem raw_values_preserve (heap : Heap) (base : Address) (count : Nat) (bits : Nat → BitVec 64)
    (stored : TensorView.Writable heap base count) :
    CStorage.Preserves heap (prepareRawValues heap base count bits) ∧
    CReadOnly.Preserves heap (prepareRawValues heap base count bits) ∧
    CAtomicBoolean.Preserves heap (prepareRawValues heap base count bits) := by
  have run := raw_values_run heap base count bits stored
  have preserved := ArrayStore.run_preserves run
  exact ⟨preserved.1, preserved.2,
    CStoreInvariant.array_run CAtomicBoolean.ordinary_stable (fun a b => a.trans b) run⟩

end Rumoca.FMI3.Float64Buffers
