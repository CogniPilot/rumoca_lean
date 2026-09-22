import RumocaC.TensorDiagonalMemory

namespace Rumoca.CTensor.Diagonal
open CMemory CMemory.TensorView Rumoca.Tensor

theorem scatter_writable (heap : Heap) (base : Address) (values : Values shape)
    (count k : Nat) (writable : Writable heap base count) :
    Writable (scatter heap base values k) base count := by
  induction k with
  | zero => exact writable
  | succ k ih =>
    rw [scatter]
    split
    · rename_i hk
      intro i hi
      by_cases same : base.index i = base.index (position shape k)
      · exact ⟨some (.finite values[k]), by simp [same]⟩
      · obtain ⟨old, found⟩ := ih i hi
        exact ⟨old, (replace_other _ _ _ _ same).trans found⟩
    · exact ih

theorem result_writable (heap : Heap) (base : Address) (values : Values shape) :
    Writable (resultHeap heap base values) base (matrixShape shape.volume shape.volume).volume :=
  scatter_writable _ base values _ _ (zero_writable heap base shape)

end Rumoca.CTensor.Diagonal
