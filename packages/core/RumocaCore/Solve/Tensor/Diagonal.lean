import RumocaCore.Solve.Tensor
import RumocaCore.Tensor.Matrix
import Mathlib.Data.Matrix.Diagonal

/-! A prepared diagonal tensor observation. Solve owns the coefficient
program and the materialization operation; a backend only renders them.
Construction adds one tensor operation, irrespective of matrix dimensions.
Dense materialization uses the existing proved mathlib matrix/storage bridge.
The first source consumer is the explicit Jacobian output of a pointwise
square. This is not a generic Jacobian synthesis or higher-derivative API. -/
namespace Rumoca.Solve.Tensor
open Rumoca.Tensor

structure DiagonalProgram (Γ : List Shape) (shape : Shape) where
  coefficients : Program Γ shape
  deriving Repr

def DiagonalProgram.shape (_ : DiagonalProgram Γ s) : Shape := matrixShape s.volume s.volume

def DiagonalProgram.eval (p : DiagonalProgram Γ s) (ops : ScalarOps α) (zero one : α)
    (env : Env α Γ) : Value α p.shape :=
  let coefficients := p.coefficients.eval ops zero one env
  letI : Zero α := ⟨zero⟩
  Value.ofMatrix (Matrix.diagonal (fun i => coefficients[i]))

def DiagonalProgram.denote (p : DiagonalProgram Γ s) (ops : ScalarOps α) (zero one : α)
    (env : SpecEnv α Γ) : Matrix (Fin s.volume) (Fin s.volume) α :=
  Matrix.of fun i j => if i = j then p.coefficients.denote ops zero one env i else zero

/-- The actual dense result has the independently specified matrix entries,
including off-diagonal zeros. No positive-extent premise excludes empty tensors. -/
theorem DiagonalProgram.eval_correct (p : DiagonalProgram Γ s) (ops : ScalarOps α) (zero one : α)
    (env : Env α Γ) :
    (p.eval ops zero one env).toMatrix = p.denote ops zero one (fun r i => (env r)[i]) := by
  ext i j
  simp only [eval, Value.toMatrix_ofMatrix, denote, Matrix.diagonal, Matrix.of_apply]
  split_ifs
  · exact p.coefficients.eval_correct ops zero one env i
  · rfl

def DiagonalProgram.nodeCount (p : DiagonalProgram Γ s) : Nat := p.coefficients.nodeCount + 1

end Rumoca.Solve.Tensor
