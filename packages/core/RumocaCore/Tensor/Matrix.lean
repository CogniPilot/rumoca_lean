import RumocaCore.Tensor
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-! Reuse mathlib's matrix algebra as the rank-two semantic view. Only the
storage/view bridge is ours; no matrix operations or laws are reimplemented.
This does not add matrix syntax or arithmetic instructions to the compiler. -/
namespace Rumoca.Tensor

def matrixShape (rows columns : Nat) : Shape := ⟨[rows, columns]⟩

def matrixIndex : Fin rows × Fin columns ≃ Fin (matrixShape rows columns).volume :=
  finProdFinEquiv.trans (finCongr (by simp [matrixShape, Shape.volume]))

def Value.toMatrix (value : Value α (matrixShape rows columns)) : Matrix (Fin rows) (Fin columns) α :=
  Matrix.of fun i j => value[matrixIndex (i, j)]

def Value.ofMatrix (value : Matrix (Fin rows) (Fin columns) α) : Value α (matrixShape rows columns) :=
  ⟨Vector.ofFn fun i => value (matrixIndex.symm i).1 (matrixIndex.symm i).2⟩

@[simp] theorem Value.ofMatrix_get (value : Matrix (Fin rows) (Fin columns) α)
    (i : Fin (matrixShape rows columns).volume) :
    (ofMatrix value)[i] = value (matrixIndex.symm i).1 (matrixIndex.symm i).2 := by
  change (Vector.ofFn _)[i] = _
  simp

@[simp] theorem Value.toMatrix_ofMatrix (value : Matrix (Fin rows) (Fin columns) α) :
    (ofMatrix value).toMatrix = value := by
  ext i j
  change (ofMatrix value)[matrixIndex (i, j)] = value i j
  simpa only [Equiv.symm_apply_apply] using ofMatrix_get value (matrixIndex (i, j))

@[simp] theorem Value.ofMatrix_toMatrix (value : Value α (matrixShape rows columns)) :
    ofMatrix value.toMatrix = value := by
  apply Value.ext
  intro i hi
  have h := ofMatrix_get value.toMatrix ⟨i, hi⟩
  simpa [toMatrix] using h

/-- All existing mathlib matrix operations and theorems can be used through
this equivalence without making the runtime evaluator depend on mathlib. -/
def matrixEquiv : Value α (matrixShape rows columns) ≃ Matrix (Fin rows) (Fin columns) α where
  toFun := Value.toMatrix
  invFun := Value.ofMatrix
  left_inv := Value.ofMatrix_toMatrix
  right_inv := Value.toMatrix_ofMatrix

end Rumoca.Tensor
