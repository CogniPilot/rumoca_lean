import RumocaC.TensorDiagonalMemory

/-! Diagonal storage for arbitrary binary64 encodings, including infinities.
The region/index model is shared with the finite diagonal view; this module
generalizes its stored values rather than changing allocation or address rules. -/
namespace Rumoca.CTensor.EncodedDiagonal
open CMemory CMemory.TensorView Rumoca.Tensor
open Diagonal (position position_bound position_index position_injective zeroHeap)

abbrev Bits (shape : Shape) := Tensor.Value (BitVec 64) shape

def ReadsBits (heap : Heap) (base : Address) (values : Bits shape) : Prop :=
  ∀ i : Fin shape.volume, load heap (base.index i.val) = some (.float64 values[i])

def matrix (values : Bits shape) : Bits (matrixShape shape.volume shape.volume) :=
  Value.ofMatrix (Matrix.diagonal (fun i => values[i]))

theorem matrix_get (values : Bits shape) (i j : Fin shape.volume) :
    (matrix values)[matrixIndex (i, j)] = if i = j then values[i] else 0 := by
  unfold matrix
  rw [Tensor.Value.ofMatrix_get]
  simp only [Equiv.symm_apply_apply, Matrix.diagonal, Matrix.of_apply]

def scatter (heap : Heap) (base : Address) (values : Bits shape) : Nat → Heap
  | 0 => heap
  | k + 1 => if h : k < shape.volume then
      replace (scatter heap base values k) (base.index (position shape k))
        ⟨.float64, true, some (.float64 values[k])⟩
    else scatter heap base values k

theorem scatter_at (heap : Heap) (base : Address) (values : Bits shape)
    (k : Nat) (bound : k ≤ shape.volume) (i : Fin shape.volume) :
    scatter heap base values k (base.index (position shape i.val)) =
      if i.val < k then some ⟨.float64, true, some (.float64 values[i])⟩
      else heap (base.index (position shape i.val)) := by
  induction k with
  | zero => simp [scatter]
  | succ k ih =>
    have hk : k < shape.volume := by omega
    rw [scatter, dif_pos hk]
    by_cases hi : i.val = k
    · have eq : i = ⟨k, hk⟩ := Fin.ext hi
      subst i
      simp [replace]
    · have hn : base.index (position shape i.val) ≠ base.index (position shape k) :=
        fun eq => hi (position_injective shape (index_injective base eq))
      rw [replace_other _ _ _ _ hn, ih (by omega)]
      have eq : i.val < k + 1 ↔ i.val < k := by omega
      simp only [eq]

theorem scatter_frame (heap : Heap) (base : Address) (values : Bits shape) (k : Nat) (q : Address)
    (outside : ∀ i < shape.volume, q ≠ base.index (position shape i)) :
    scatter heap base values k q = heap q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [scatter]
    split
    · rw [replace_other _ _ _ _ (outside k ‹_›), ih]
    · exact ih

theorem scatter_store_next (heap : Heap) (base : Address) (values : Bits shape)
    (writable : Writable heap base (matrixShape shape.volume shape.volume).volume)
    (i : Fin shape.volume) :
    store (scatter heap base values i.val) (base.index (position shape i.val)) (.float64 values[i]) =
      some (scatter heap base values (i.val + 1)) := by
  obtain ⟨old, ho⟩ := writable (position shape i.val) (position_bound i)
  have cell := scatter_at heap base values i.val (by omega) i
  rw [if_neg (by omega)] at cell
  have stored := store_float64 _ _ old values[i] (cell.trans ho)
  simpa only [scatter, dif_pos i.isLt, Fin.getElem_fin] using stored

def resultHeap (heap : Heap) (base : Address) (values : Bits shape) : Heap :=
  scatter (zeroHeap heap base shape) base values shape.volume

theorem result_reads (heap : Heap) (base : Address) (values : Bits shape) :
    ReadsBits (resultHeap heap base values) base (matrix values) := by
  intro index
  obtain ⟨⟨i, j⟩, rfl⟩ := matrixIndex.surjective index
  rw [matrix_get]
  by_cases eq : i = j
  · subst j
    have cell := scatter_at (zeroHeap heap base shape) base values shape.volume (by omega) i
    rw [if_pos i.isLt, position_index] at cell
    simp only [resultHeap, load, cell, bind, Option.bind_some, convert,
      show (CType.float64 = CType.atomicBoolean) = False from by decide +kernel, ↓reduceIte, pure]
  · have outside : ∀ k < shape.volume,
        base.index (matrixIndex (i, j)).val ≠ base.index (position shape k) := by
      intro k hk same
      rw [position_index (⟨k, hk⟩ : Fin shape.volume)] at same
      have entries := matrixIndex.injective (Fin.ext (index_injective base same))
      exact eq ((congrArg Prod.fst entries).trans (congrArg Prod.snd entries).symm)
    have cell := scatter_frame (zeroHeap heap base shape) base values shape.volume _ outside
    have zeros := written_reads heap base
      (Tensor.Value.fill (matrixShape shape.volume shape.volume) Binary64.positiveZero) (matrixIndex (i, j))
    rw [if_neg eq]
    simp only [resultHeap, load, cell]
    simpa only [load, Fin.getElem_fin, Tensor.Value.getElem_fill, CMemory.Value.finite,
      show (Binary64.toBits Binary64.positiveZero).val = (0 : BitVec 64) from by decide +kernel]
      using zeros

theorem result_frame (heap : Heap) (base : Address) (values : Bits shape) (q : Address)
    (outside : ∀ i < (matrixShape shape.volume shape.volume).volume, q ≠ base.index i) :
    resultHeap heap base values q = heap q := by
  rw [resultHeap, scatter_frame _ _ _ _ _ (fun i hi => outside _ (position_bound ⟨i, hi⟩))]
  exact written_frame _ _ _ _ _ outside

theorem coeff_reads (heap : Heap) (output input : Address) (result : Bits shape)
    (values : Values shape) (k : Nat)
    (separate : Diagonal.Separate output input shape) (reads : Reads heap input values) :
    Reads (scatter (zeroHeap heap output shape) output result k) input values := by
  intro i
  have copied := scatter_frame (zeroHeap heap output shape) output result k (input.index i.val)
    (fun j hj => Ne.symm (separate _ (position_bound ⟨j, hj⟩) i.val i.isLt))
  have zeroed := written_frame heap output
    (Tensor.Value.fill (matrixShape shape.volume shape.volume) Binary64.positiveZero)
    (matrixShape shape.volume shape.volume).volume (input.index i.val)
    (fun j hj => Ne.symm (separate j hj i.val i.isLt))
  simp only [load, copied]
  simpa only [zeroHeap, zeroed, load] using reads i

/-- Finite storage is exactly the specialization of the encoded view. -/
def finiteBits (values : Values shape) : Bits shape :=
  ⟨values.data.map (fun x => (Binary64.toBits x).val)⟩

theorem finiteBits_get (values : Values shape) (i : Nat) (hi : i < shape.volume) :
    (finiteBits values)[i] = (Binary64.toBits values[i]).val := by
  exact Vector.getElem_map _ _

theorem scatter_finite (heap : Heap) (base : Address) (values : Values shape) (k : Nat) :
    scatter heap base (finiteBits values) k = Diagonal.scatter heap base values k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [scatter, Diagonal.scatter, ih]
    split
    · simp only [finiteBits_get, CMemory.Value.finite]
    · rfl

theorem resultHeap_finite (heap : Heap) (base : Address) (values : Values shape) :
    resultHeap heap base (finiteBits values) = Diagonal.resultHeap heap base values :=
  scatter_finite _ _ _ _

end Rumoca.CTensor.EncodedDiagonal
