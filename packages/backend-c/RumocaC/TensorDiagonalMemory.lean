import RumocaC.TensorMemory
import RumocaCore.Solve.Tensor.Diagonal
import RumocaCore.Solve.Tensor.Finite

/-! Exact diagonal copies over the shared symbolic object memory. Mathlib's
matrix/storage equivalence supplies the row-major index map. Off-diagonal
cells receive positive zero; coefficient bit patterns are preserved. -/
namespace Rumoca.CTensor.Diagonal
open CMemory CMemory.TensorView Rumoca.Tensor

def matrix (values : Values shape) : Values (matrixShape shape.volume shape.volume) :=
  letI : Zero Binary64.Value := ⟨Binary64.positiveZero⟩
  Value.ofMatrix (Matrix.diagonal (fun i => values[i]))

theorem matrix_get (values : Values shape) (i j : Fin shape.volume) :
    (matrix values)[matrixIndex (i, j)] = if i = j then values[i] else Binary64.positiveZero := by
  unfold matrix
  rw [Tensor.Value.ofMatrix_get]
  simp only [Equiv.symm_apply_apply, Matrix.diagonal, Matrix.of_apply]
  rfl

def position (shape : Shape) (i : Nat) : Nat := i * (shape.volume + 1)

theorem matrix_index (i : Fin rows) (j : Fin columns) :
    (matrixIndex (i, j)).val = i.val * columns + j.val := by
  change j.val + columns * i.val = i.val * columns + j.val
  ac_rfl

theorem position_index (i : Fin shape.volume) :
    position shape i.val = (matrixIndex (i, i)).val := by
  rw [matrix_index]
  simp [position, Nat.mul_add]

theorem position_bound (i : Fin shape.volume) :
    position shape i.val < (matrixShape shape.volume shape.volume).volume := by
  rw [position_index]
  exact (matrixIndex (i, i)).isLt

theorem position_injective (shape : Shape) : Function.Injective (position shape) := by
  intro i j eq
  exact Nat.eq_of_mul_eq_mul_right (by omega) eq

theorem counter_bounds (shape : Shape)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) :
    shape.volume < 2 ^ 64 ∧ shape.volume + 1 < 2 ^ 64 ∧ position shape shape.volume < 2 ^ 64 := by
  have area : shape.volume * shape.volume < 18446744073709551616 := by
    simpa [matrixShape, Shape.volume] using bounded
  have dimension : shape.volume ≤ 4294967295 := by nlinarith
  have product := Nat.mul_le_mul dimension (show shape.volume + 1 ≤ 4294967296 by omega)
  exact ⟨by omega, by omega, by simpa only [position] using (show
    shape.volume * (shape.volume + 1) < 2 ^ 64 by omega)⟩

theorem position_bounded (shape : Shape)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64)
    (i : Nat) (hi : i ≤ shape.volume) : position shape i < 2 ^ 64 :=
  lt_of_le_of_lt (Nat.mul_le_mul_right (shape.volume + 1) hi) (counter_bounds shape bounded).2.2

def scatter (heap : Heap) (base : Address) (values : Values shape) : Nat → Heap
  | 0 => heap
  | k + 1 => if h : k < shape.volume then
      replace (scatter heap base values k) (base.index (position shape k))
        ⟨.float64, true, some (.finite values[k])⟩
    else scatter heap base values k

theorem scatter_at (heap : Heap) (base : Address) (values : Values shape)
    (k : Nat) (bound : k ≤ shape.volume) (i : Fin shape.volume) :
    scatter heap base values k (base.index (position shape i.val)) =
      if i.val < k then some ⟨.float64, true, some (.finite values[i])⟩
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

theorem scatter_frame (heap : Heap) (base : Address) (values : Values shape) (k : Nat) (q : Address)
    (outside : ∀ i < shape.volume, q ≠ base.index (position shape i)) :
    scatter heap base values k q = heap q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [scatter]
    split
    · rw [replace_other _ _ _ _ (outside k ‹_›), ih]
    · exact ih

theorem scatter_store_next (heap : Heap) (base : Address) (values : Values shape)
    (writable : Writable heap base (matrixShape shape.volume shape.volume).volume)
    (i : Fin shape.volume) :
    store (scatter heap base values i.val) (base.index (position shape i.val)) (.finite values[i]) =
      some (scatter heap base values (i.val + 1)) := by
  obtain ⟨old, ho⟩ := writable (position shape i.val) (position_bound i)
  have cell := scatter_at heap base values i.val (by omega) i
  rw [if_neg (by omega)] at cell
  have stored := store_float64 _ _ old (Binary64.toBits values[i]).val (cell.trans ho)
  simpa only [Value.finite, scatter, dif_pos i.isLt, Fin.getElem_fin] using stored

def zeroHeap (heap : Heap) (base : Address) (shape : Shape) : Heap :=
  written heap base (Tensor.Value.fill (matrixShape shape.volume shape.volume) Binary64.positiveZero)
    (matrixShape shape.volume shape.volume).volume

def resultHeap (heap : Heap) (base : Address) (values : Values shape) : Heap :=
  scatter (zeroHeap heap base shape) base values shape.volume

theorem zero_writable (heap : Heap) (base : Address) (shape : Shape) :
    Writable (zeroHeap heap base shape) base (matrixShape shape.volume shape.volume).volume := by
  intro k hk
  refine ⟨some (.finite Binary64.positiveZero), ?_⟩
  simpa [zeroHeap, hk] using
    written_at heap base (Tensor.Value.fill (matrixShape shape.volume shape.volume) Binary64.positiveZero)
      (matrixShape shape.volume shape.volume).volume (by omega) ⟨k, hk⟩

theorem result_reads (heap : Heap) (base : Address) (values : Values shape) :
    Reads (resultHeap heap base values) base (matrix values) := by
  intro index
  obtain ⟨⟨i, j⟩, rfl⟩ := matrixIndex.surjective index
  rw [matrix_get]
  by_cases eq : i = j
  · subst j
    have cell := scatter_at (zeroHeap heap base shape) base values shape.volume (by omega) i
    rw [if_pos i.isLt, position_index] at cell
    simp only [resultHeap, load, cell, bind, Option.bind_some, convert, Value.finite,
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
    simpa only [load, Fin.getElem_fin, Tensor.Value.getElem_fill] using zeros

theorem result_frame (heap : Heap) (base : Address) (values : Values shape) (q : Address)
    (outside : ∀ i < (matrixShape shape.volume shape.volume).volume, q ≠ base.index i) :
    resultHeap heap base values q = heap q := by
  rw [resultHeap, scatter_frame _ _ _ _ _ (fun i hi => outside _ (position_bound ⟨i, hi⟩))]
  exact written_frame _ _ _ _ _ outside

def Separate (output input : Address) (shape : Shape) : Prop :=
  ∀ i < (matrixShape shape.volume shape.volume).volume, ∀ j < shape.volume,
    output.index i ≠ input.index j

theorem input_reads (heap : Heap) (output input : Address) (values : Values shape) (k : Nat)
    (separate : Separate output input shape) (reads : Reads heap input values) :
    Reads (scatter (zeroHeap heap output shape) output values k) input values := by
  intro i
  have copied := scatter_frame (zeroHeap heap output shape) output values k (input.index i.val)
    (fun j hj => Ne.symm (separate _ (position_bound ⟨j, hj⟩) i.val i.isLt))
  have zeroed := written_frame heap output
    (Tensor.Value.fill (matrixShape shape.volume shape.volume) Binary64.positiveZero)
    (matrixShape shape.volume shape.volume).volume (input.index i.val)
    (fun j hj => Ne.symm (separate j hj i.val i.isLt))
  simp only [load, copied]
  simpa only [zeroHeap, zeroed, load] using reads i

theorem solve_matrix (p : Solve.Tensor.DiagonalProgram Γ shape)
    (env : Solve.Tensor.Env Binary64.Value Γ) :
    matrix (p.coefficients.eval Solve.Tensor.Finite.ops Binary64.positiveZero Binary64.one env) =
      p.eval Solve.Tensor.Finite.ops Binary64.positiveZero Binary64.one env := rfl

end Rumoca.CTensor.Diagonal
