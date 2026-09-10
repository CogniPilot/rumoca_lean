import RumocaCore.Tensor.Operators
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

/-! Analytic correctness of shape-preserving tensor AD primitives. Forward
rules are Fréchet derivatives in mathlib; reverse rules are their adjoints under
mathlib's finite dot-product pairing. The executable rules use dense vectors.
These are mathematical Real results, not derivatives of rounded IEEE programs.
The square rule accounts for the two uses of one input. General program AD,
source built-in lowering and target execution remain separate obligations. -/
noncomputable section
namespace Rumoca.Tensor.AD

def realOps : ScalarOps ℝ := ⟨(· + ·), (· * ·)⟩
abbrev Space (s : Shape) := Denotation ℝ s

def leftCoord (i : Fin s.volume) : (Space s × Space s) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)

def rightCoord (i : Fin s.volume) : (Space s × Space s) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _)

def differential (op : BinaryOp) (x y : Space s) : (Space s × Space s) →L[ℝ] Space s :=
  ContinuousLinearMap.pi fun i => match op with
  | .add => leftCoord i + rightCoord i
  | .mul => x i • rightCoord i + y i • leftCoord i

theorem hasFDerivAt (op : BinaryOp) (x y : Space s) :
    HasFDerivAt (fun p : Space s × Space s => op.denote realOps p.1 p.2)
      (differential op x y) (x, y) := by
  apply hasFDerivAt_pi.mpr
  intro i
  cases op
  · exact (leftCoord i).hasFDerivAt.add (rightCoord i).hasFDerivAt
  · exact (leftCoord i).hasFDerivAt (x := (x, y)) |>.mul ((rightCoord i).hasFDerivAt (x := (x, y)))

theorem jvp_correct (op : BinaryOp) (x y dx dy : Value ℝ s) (i : Fin s.volume) :
    (op.jvp realOps x y dx dy)[i] =
      differential op (fun j => x[j]) (fun j => y[j]) ((fun j => dx[j]), (fun j => dy[j])) i := by
  cases op <;> simp [BinaryOp.jvp, BinaryOp.eval, BinaryOp.scalar, realOps, differential, leftCoord, rightCoord]

theorem vjp_correct (op : BinaryOp) (x y seed : Value ℝ s) (dx dy : Space s) :
    dotProduct (fun i => seed[i]) (differential op (fun i => x[i]) (fun i => y[i]) (dx, dy)) =
      dotProduct (fun i => (op.vjp realOps x y seed).1[i]) dx +
      dotProduct (fun i => (op.vjp realOps x y seed).2[i]) dy := by
  simp only [dotProduct, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases op <;>
    simp [BinaryOp.vjp, BinaryOp.eval, BinaryOp.scalar, realOps,
      differential, leftCoord, rightCoord] <;> ring

/-- Duplicating an input in a nonlinear expression contributes along both edges. -/
def squareDifferential (x : Space s) : Space s →L[ℝ] Space s :=
  (differential .mul x x).comp ((ContinuousLinearMap.id ℝ _).prod (ContinuousLinearMap.id ℝ _))

theorem square_hasFDerivAt (x : Space s) :
    HasFDerivAt (fun v : Space s => BinaryOp.denote realOps .mul v v)
      (squareDifferential x) x := by
  exact (hasFDerivAt .mul x x).comp (f := fun v : Space s => (v, v)) x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_id x))

def squarePullback (x seed : Value ℝ s) : Value ℝ s :=
  let cotangents := BinaryOp.vjp realOps .mul x x seed
  BinaryOp.eval realOps .add cotangents.1 cotangents.2

theorem square_vjp_correct (x seed : Value ℝ s) (dx : Space s) :
    dotProduct (fun i => seed[i]) (squareDifferential (fun i => x[i]) dx) =
      dotProduct (fun i => (squarePullback x seed)[i]) dx := by
  have h := vjp_correct .mul x x seed dx dx
  simpa [squareDifferential, squarePullback, BinaryOp.eval, BinaryOp.scalar,
    realOps, dotProduct, add_mul, Finset.sum_add_distrib] using h

/-- Mathematical matrix view of the square operator's derivative. The compiler
can retain the diagonal as a tensor operator rather than expanding matrix entries. -/
def squareJacobian (x : Space s) : Matrix (Fin s.volume) (Fin s.volume) ℝ :=
  Matrix.diagonal (fun i => x i + x i)

theorem square_jacobian_correct (x dx : Space s) :
    Matrix.mulVec (squareJacobian x) dx = squareDifferential x dx := by
  funext i
  simp [squareJacobian, Matrix.mulVec_diagonal, squareDifferential, differential,
    leftCoord, rightCoord, add_mul]

end Rumoca.Tensor.AD
