import RumocaC.ArrayStore

/-! Rank-preserving binary64 bit views over the existing typed array-store
model. Finite numbers and infinities share the same C cells; no new allocation
or address semantics is introduced. -/
namespace Rumoca.CMemory.EncodedTensor
open TensorView Rumoca.Tensor

abbrev Bits (shape : Shape) := Tensor.Value (BitVec 64) shape

def ReadsBits (heap : Heap) (base : Address) (values : Bits shape) : Prop :=
  ∀ i : Fin shape.volume, load heap (base.index i.val) = some (.float64 values[i])

def written (heap : Heap) (base : Address) (values : Bits shape) : Nat → Heap :=
  ArrayStore.written heap base .float64 (fun i => .float64 values[i])

theorem written_frame (heap : Heap) (base : Address) (values : Bits shape) (k : Nat) (q : Address)
    (outside : ∀ i < shape.volume, q ≠ base.index i) : written heap base values k q = heap q :=
  ArrayStore.frame _ _ _ _ _ _ (fun i => outside i.val i.isLt)

theorem written_reads (heap : Heap) (base : Address) (values : Bits shape) :
    ReadsBits (written heap base values shape.volume) base values :=
  ArrayStore.written_reads heap base .float64 (fun i => .float64 values[i])
    (by decide +kernel) (fun _ => rfl)

theorem reads_written (heap : Heap) (output input : Address) (values : Bits shape)
    (original : Values shape) (k : Nat)
    (separate : Separate output input shape.volume) (reads : Reads heap input original) :
    Reads (written heap output values k) input original := by
  intro i
  have frame := written_frame heap output values k (input.index i.val)
    (fun j hj => Ne.symm (separate j hj i.val i.isLt))
  simpa only [load, frame] using reads i

theorem store_next (heap : Heap) (base : Address) (values : Bits shape)
    (writable : Writable heap base shape.volume) (i : Fin shape.volume) :
    store (written heap base values i.val) (base.index i.val) (.float64 values[i]) =
      some (written heap base values (i.val + 1)) := by
  obtain ⟨old, found⟩ := writable i.val i.isLt
  have cell := ArrayStore.written_at heap base .float64 (fun j => .float64 values[j])
    i.val (by omega) i
  rw [if_neg (by omega)] at cell
  have stored := store_float64 _ _ old values[i] (cell.trans found)
  simpa only [written, ArrayStore.written, dif_pos i.isLt] using stored

def finiteBits (values : Values shape) : Bits shape :=
  ⟨values.data.map (fun x => (Binary64.toBits x).val)⟩

theorem finiteBits_get (values : Values shape) (i : Nat) (hi : i < shape.volume) :
    (finiteBits values)[i] = (Binary64.toBits values[i]).val :=
  Vector.getElem_map _ _

/-- The old finite tensor heap is an exact instance of the shared store model. -/
theorem written_finite (heap : Heap) (base : Address) (values : Values shape) (k : Nat) :
    written heap base (finiteBits values) k = TensorView.written heap base values k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ArrayStore.written heap base .float64 (fun i => .float64 (finiteBits values)[i]) (k + 1) = _
    rw [ArrayStore.written, TensorView.written]
    change (if h : k < shape.volume then
      replace (written heap base (finiteBits values) k) (base.index k)
        ⟨.float64, true, some (.float64 (finiteBits values)[k])⟩
      else written heap base (finiteBits values) k) = _
    rw [ih]
    split
    · simp only [finiteBits_get, CMemory.Value.finite]
    · rfl

end Rumoca.CMemory.EncodedTensor
