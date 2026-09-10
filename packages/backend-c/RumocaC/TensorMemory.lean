import RumocaC.Memory
import RumocaCore.Tensor

/-! Dense tensor views of symbolic C array cells. Input arrays may alias each
other; output writes require a separate range. Uninitialized writable output
cells are supported. The frame theorem covers the entire remaining heap. -/
namespace Rumoca.CMemory.TensorView

abbrev Values (shape : Rumoca.Tensor.Shape) := Rumoca.Tensor.Value Binary64.Value shape

def Reads (heap : Heap) (base : Address) (values : Values shape) : Prop :=
  ∀ i : Fin shape.volume, load heap (base.index i.val) = some (.finite values[i])

def Writable (heap : Heap) (base : Address) (count : Nat) : Prop :=
  ∀ i < count, ∃ old, heap (base.index i) = some ⟨.float64, true, old⟩

def Separate (output input : Address) (count : Nat) : Prop :=
  ∀ i < count, ∀ j < count, output.index i ≠ input.index j

theorem index_injective (base : Address) : Function.Injective base.index := by
  intro i j h
  have ho := congrArg Address.offset h
  simp only [Address.index] at ho
  omega

def written (heap : Heap) (base : Address) (values : Values shape) : Nat → Heap
  | 0 => heap
  | k + 1 => if h : k < shape.volume then
      replace (written heap base values k) (base.index k) ⟨.float64, true, some (.finite values[k])⟩
    else written heap base values k

theorem written_at (heap : Heap) (base : Address) (values : Values shape)
    (k : Nat) (bound : k ≤ shape.volume) (i : Fin shape.volume) :
    written heap base values k (base.index i.val) =
      if i.val < k then some ⟨.float64, true, some (.finite values[i])⟩ else heap (base.index i.val) := by
  induction k with
  | zero => simp [written]
  | succ k ih =>
    have hk : k < shape.volume := by omega
    rw [written, dif_pos hk]
    by_cases hi : i.val = k
    · have he : i = ⟨k, hk⟩ := Fin.ext hi
      subst i
      simp [replace]
    · have hn : base.index i.val ≠ base.index k := fun h => hi (index_injective base h)
      rw [replace_other _ _ _ _ hn, ih (by omega)]
      have he : i.val < k + 1 ↔ i.val < k := by omega
      simp only [he]

theorem written_frame (heap : Heap) (base : Address) (values : Values shape) (k : Nat) (q : Address)
    (outside : ∀ i < shape.volume, q ≠ base.index i) : written heap base values k q = heap q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [written]
    split
    · rw [replace_other _ _ _ _ (outside k ‹_›), ih]
    · exact ih

theorem reads_written (heap : Heap) (output input : Address) (values original : Values shape) (k : Nat)
    (separate : Separate output input shape.volume) (reads : Reads heap input original) :
    Reads (written heap output values k) input original := by
  intro i
  have hf := written_frame heap output values k (input.index i.val)
    (fun j hj => Ne.symm (separate j hj i.val i.isLt))
  simpa only [load, hf] using reads i

theorem store_next (heap : Heap) (base : Address) (values : Values shape)
    (writable : Writable heap base shape.volume) (k : Nat) (bound : k < shape.volume) :
    store (written heap base values k) (base.index k) (.finite values[k]) =
      some (written heap base values (k + 1)) := by
  obtain ⟨old, ho⟩ := writable k bound
  have he := written_at heap base values k (by omega) ⟨k, bound⟩
  simp only [lt_self_iff_false, if_false] at he
  have hs := store_float64 (written heap base values k) (base.index k) old (Binary64.toBits values[k]).val
    (he.trans ho)
  simpa only [Value.finite, written, dif_pos bound] using hs

theorem written_reads (heap : Heap) (base : Address) (values : Values shape) :
    Reads (written heap base values shape.volume) base values := by
  intro i
  have he := written_at heap base values shape.volume (by omega) i
  rw [if_pos i.isLt] at he
  simp [load, he, convert, Value.finite]

end Rumoca.CMemory.TensorView
