import RumocaCore.Solve.Tensor.Reverse
import RumocaCore.Solve.Tensor.Differentiation

/-! The reverse evaluator is the adjoint of the same program derivative used
by forward AD. A dependent environment pairing sums over tensor registers,
then mathlib's dot product pairs the coordinates of each register. -/
noncomputable section
namespace Rumoca.Solve.Tensor
open Rumoca.Tensor

def Env.pair : {Γ : List Shape} → Env ℝ Γ → SpecEnv ℝ Γ → ℝ
  | [], _, _ => 0
  | _ :: _, cotangent, tangent =>
      dotProduct (fun i => (cotangent .here)[i]) (tangent .here) +
        Env.pair cotangent.tail (fun r => tangent (.there r))

theorem Env.pair_zeros (tangent : SpecEnv ℝ Γ) : Env.pair (Env.zeros 0) tangent = 0 := by
  induction Γ with
  | nil => rfl
  | cons s Γ ih => simpa [pair, zeros, tail, dotProduct] using ih (fun r => tangent (.there r))

/-- Accumulating at one reference changes the pairing by exactly that
reference's contribution. No distinctness premise is needed. -/
theorem Env.pair_addAt (r : Ref Γ s) (value : Value ℝ s) (env : Env ℝ Γ)
    (tangent : SpecEnv ℝ Γ) :
    Env.pair (env.addAt AD.realOps r value) tangent =
      env.pair tangent + dotProduct (fun i => value[i]) (tangent r) := by
  induction r with
  | @here shape Γ =>
    change dotProduct (fun i : Fin shape.volume => (BinaryOp.eval AD.realOps .add (env .here) value)[i.val]) _ +
      Env.pair env.tail _ = (dotProduct _ _ + Env.pair env.tail _) + _
    simp only [Fin.getElem_fin, BinaryOp.eval, Value.getElem_zipWith, BinaryOp.scalar, AD.realOps,
      dotProduct, add_mul, Finset.sum_add_distrib]
    ring
  | there r ih =>
    change dotProduct _ _ + Env.pair (Env.addAt AD.realOps r value env.tail) _ =
      (dotProduct _ _ + Env.pair env.tail _) + _
    rw [ih]
    simp only [Env.addAt, Env.push]
    ring

/-- Every backwards sweep transposes the complete forward sweep, including
shared operands, reused intermediates and unused registers. -/
theorem Program.reverse_pairing (p : Program Γ s) (env tangent : Env ℝ Γ) (seed : Value ℝ s) :
    dotProduct (fun i : Fin s.volume => seed[i]) (fun i => (p.evalForward AD.realOps 0 1 env tangent).2[i]) =
      Env.pair ((p.reverse AD.realOps 0 1 env).pullback seed) tangent.denote := by
  induction p with
  | ret r =>
    simp only [reverse, evalForward, Env.pair_addAt, Env.pair_zeros, zero_add]
    rfl
  | fill shape value next ih =>
    have hn := ih (env.push (Value.fill shape (value.eval 0 1)))
      (tangent.push (Value.fill shape 0)) seed
    simpa [reverse, evalForward, Env.pair, Env.denote, Env.push, dotProduct] using hn
  | @binary Γ shape s op left right next ih =>
    have hn := ih (env.push (op.eval AD.realOps (env left) (env right)))
      (tangent.push (op.jvp AD.realOps (env left) (env right) (tangent left) (tangent right))) seed
    let bars : Env ℝ (_ :: _) :=
      (next.reverse AD.realOps 0 1 (env.push (op.eval AD.realOps (env left) (env right)))).pullback seed
    have hop : dotProduct (fun i : Fin shape.volume => (bars .here)[i])
        (fun i => (op.jvp AD.realOps (env left) (env right) (tangent left) (tangent right))[i]) =
        dotProduct (fun i : Fin shape.volume => (op.vjp AD.realOps (env left) (env right) (bars .here)).1[i])
          (fun i => (tangent left)[i]) +
        dotProduct (fun i : Fin shape.volume => (op.vjp AD.realOps (env left) (env right) (bars .here)).2[i])
          (fun i => (tangent right)[i]) := by
      simp only [AD.jvp_correct]
      exact AD.vjp_correct op (env left) (env right) (bars .here) _ _
    change _ = Env.pair (Env.addAt AD.realOps right _ (Env.addAt AD.realOps left _ bars.tail)) _
    rw [Env.pair_addAt, Env.pair_addAt]
    change _ = Env.pair bars.tail tangent.denote + _ + _
    change dotProduct _ (fun i : Fin s.volume => (next.evalForward AD.realOps 0 1 _ _).2[i]) = _
    rw [hn]
    change dotProduct (fun i : Fin shape.volume => (bars .here)[i])
      (fun i => (op.jvp AD.realOps (env left) (env right) (tangent left) (tangent right))[i]) +
        Env.pair bars.tail tangent.denote = _
    rw [hop]
    exact (add_comm _ _).trans (add_assoc _ _ _).symm

/-- Analytic consequence: reverse execution pairs with the Fréchet
derivative, not merely with another syntactic differentiation algorithm. -/
theorem Program.reverse_differential (p : Program Γ s) (env tangent : Env ℝ Γ)
    (df : LinearEnv input Γ) (dx : AD.Space input) (seed : Value ℝ s)
    (h : ∀ {t} (r : Ref Γ t) (i : Fin t.volume), (tangent r)[i] = df r dx i) :
    dotProduct (fun i => seed[i]) (p.differential env.denote df dx) =
      Env.pair ((p.reverse AD.realOps 0 1 env).pullback seed) tangent.denote := by
  have hd := funext (p.evalForward_tangent env tangent df dx h)
  rw [← hd]
  exact p.reverse_pairing env tangent seed

/-- Source denotation and saved-tape execution agree on the action of a true
Fréchet derivative, for arbitrary entry functions and output cotangents. -/
theorem Program.reverse_derivative (p : Program Γ s) (env tangent : Env ℝ Γ)
    (f : AD.Space input → SpecEnv ℝ Γ) (df : LinearEnv input Γ)
    (x dx : AD.Space input) (seed : Value ℝ s) (hreg : p.RegularAt (f x))
    (hf : ∀ {t} (r : Ref Γ t), HasFDerivAt (fun x => f x r) (df r) x)
    (hp : ∀ {t} (r : Ref Γ t) (i : Fin t.volume), (env r)[i] = f x r i)
    (ht : ∀ {t} (r : Ref Γ t) (i : Fin t.volume), (tangent r)[i] = df r dx i) :
    ∃ derivative : AD.Space input →L[ℝ] AD.Space s,
      HasFDerivAt (fun x => p.denote AD.realOps 0 1 (f x)) derivative x ∧
      dotProduct (fun i => seed[i]) (derivative dx) =
        Env.pair ((p.reverse AD.realOps 0 1 env).pullback seed) tangent.denote := by
  refine ⟨p.differential (f x) df, p.hasFDerivAt f df x hreg hf, ?_⟩
  have hd := p.reverse_differential env tangent df dx seed ht
  have he : (env.denote : SpecEnv ℝ Γ) = (fun {t} (r : Ref Γ t) => f x r) := by
    funext t r i
    exact hp r i
  rw [he] at hd
  exact hd

end Rumoca.Solve.Tensor
