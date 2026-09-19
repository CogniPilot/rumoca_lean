import RumocaCore.Solve.Tensor.Forward
import RumocaCore.Tensor.Differentiation

/-! Analytic correctness for arbitrary typed tensor programs. Register
functions may depend on a shared input space; the chain rule composes their
Fréchet derivatives. This includes aliasing and nonlinear intermediate values,
with no assumption that different register references are independent. -/
noncomputable section
namespace Rumoca.Solve.Tensor
open Rumoca.Tensor

abbrev LinearEnv (input : Shape) (Γ : List Shape) :=
  {s : Shape} → Ref Γ s → AD.Space input →L[ℝ] AD.Space s

def LinearEnv.push (value : AD.Space input →L[ℝ] AD.Space s)
    (env : LinearEnv input Γ) : LinearEnv input (s :: Γ)
  | _, .here => value
  | _, .there r => env r

def Program.differential : Program Γ s → SpecEnv ℝ Γ → LinearEnv input Γ →
    AD.Space input →L[ℝ] AD.Space s
  | .ret r, _, tangent => tangent r
  | .fill _ value next, env, tangent =>
      next.differential (env.push (fun _ => value.eval 0 1)) (tangent.push 0)
  | .binary op left right next, env, tangent =>
      next.differential (env.push (op.denote AD.realOps (env left) (env right)))
        (tangent.push ((AD.differential op (env left) (env right)).comp
          ((tangent left).prod (tangent right))))

/-- Every binary node's operands are regular at the primal denotation. Only a
division node constrains its divisor; the smooth operators impose nothing. -/
def Program.RegularAt : (p : Program Γ s) → SpecEnv ℝ Γ → Prop
  | .ret _, _ => True
  | .fill _ value next, env => next.RegularAt (SpecEnv.push (fun _ => value.eval 0 1) env)
  | .binary op left right next, env =>
      AD.Regular op (env left) (env right) ∧
        next.RegularAt (SpecEnv.push (op.denote AD.realOps (env left) (env right)) env)

/-- A chain-rule theorem for the entire program, relative to arbitrary
differentiable register functions at its entry. Division nodes require a
nonzero divisor at the linearization point, recorded by `RegularAt`. -/
theorem Program.hasFDerivAt (p : Program Γ s) (f : AD.Space input → SpecEnv ℝ Γ)
    (df : LinearEnv input Γ) (x : AD.Space input) (hreg : p.RegularAt (f x))
    (h : ∀ {t} (r : Ref Γ t), HasFDerivAt (fun x => f x r) (df r) x) :
    HasFDerivAt (fun x => p.denote AD.realOps 0 1 (f x))
      (p.differential (f x) df) x := by
  induction p with
  | ret r => exact h r
  | fill shape value next ih =>
    refine ih (fun x => SpecEnv.push (fun _ => value.eval 0 1) (f x)) (df.push 0) hreg ?_
    intro t r
    cases r with
    | here => exact hasFDerivAt_const _ _
    | there r => exact h r
  | binary op left right next ih =>
    refine ih (fun x => SpecEnv.push (op.denote AD.realOps (f x left) (f x right)) (f x))
      (df.push ((AD.differential op (f x left) (f x right)).comp
        ((df left).prod (df right)))) hreg.2 ?_
    intro t r
    cases r with
    | here =>
      exact (AD.hasFDerivAt op (f x left) (f x right) hreg.1).comp x
        ((h left).prodMk (h right))
    | there r => exact h r

def Env.denote (env : Env α Γ) : SpecEnv α Γ := fun r i => (env r)[i]

@[simp] theorem Env.denote_push (env : Env α Γ) (value : Value α s) :
    (Env.denote (env.push value) : SpecEnv α (s :: Γ)) =
      (fun {t} (r : Ref (s :: Γ) t) => SpecEnv.push (fun i : Fin s.volume => value[i]) env.denote r) := by
  funext t r i
  cases r <;> rfl

/-- The dense evaluator computes the action of the program derivative on any
tangent. Both the input linearization and the tangent may share registers. -/
theorem Program.evalForward_tangent (p : Program Γ s) (env tangent : Env ℝ Γ)
    (df : LinearEnv input Γ) (dx : AD.Space input)
    (h : ∀ {t} (r : Ref Γ t) (i : Fin t.volume), (tangent r)[i] = df r dx i) :
    ∀ i, (p.evalForward AD.realOps 0 1 env tangent).2[i] =
      p.differential env.denote df dx i := by
  induction p with
  | ret r => exact h r
  | fill shape value next ih =>
    intro i
    have hn := ih (env.push (Value.fill shape (value.eval 0 1)))
      (tangent.push (Value.fill shape 0)) (df.push 0)
    have ht : ∀ {t} (r : Ref (shape :: _) t) (j : Fin t.volume),
        ((tangent.push (Value.fill shape 0)) r)[j] = (df.push 0) r dx j := by
      intro t r j
      cases r with
      | here => simp [Env.push, LinearEnv.push]
      | there r => exact h r j
    rw [evalForward, hn ht]
    have he : (Env.denote (env.push (Value.fill shape (value.eval 0 1))) : SpecEnv ℝ _) =
        (fun {t} (r : Ref (shape :: _) t) => SpecEnv.push (fun _ : Fin shape.volume => value.eval 0 1) env.denote r) := by
      funext t r j
      cases r <;> simp [Env.denote, Env.push, SpecEnv.push]
    exact congrArg (fun e : SpecEnv ℝ _ => next.differential e (df.push 0) dx i) he
  | binary op left right next ih =>
    intro i
    have hn := ih (env.push (op.eval AD.realOps (env left) (env right)))
      (tangent.push (op.jvp AD.realOps (env left) (env right) (tangent left) (tangent right)))
      (df.push ((AD.differential op (env.denote left) (env.denote right)).comp
        ((df left).prod (df right))))
    have ht : ∀ {t} (r : Ref (_ :: _) t) (j : Fin t.volume),
        ((tangent.push (op.jvp AD.realOps (env left) (env right) (tangent left) (tangent right))) r)[j] =
          (df.push ((AD.differential op (env.denote left) (env.denote right)).comp
            ((df left).prod (df right)))) r dx j := by
      intro t r j
      cases r with
      | here =>
        change (op.jvp AD.realOps (env left) (env right) (tangent left) (tangent right))[j] = _
        rw [AD.jvp_correct]
        have hl : (fun i : Fin _ => (tangent left)[i]) = df left dx := funext (h left)
        have hr : (fun i : Fin _ => (tangent right)[i]) = df right dx := funext (h right)
        rw [hl, hr]
        rfl
      | there r => exact h r j
    rw [evalForward, hn ht]
    have he : (Env.denote (env.push (op.eval AD.realOps (env left) (env right))) : SpecEnv ℝ _) =
        (fun {t} (r : Ref (_ :: _) t) =>
          SpecEnv.push (op.denote AD.realOps (env.denote left) (env.denote right)) env.denote r) := by
      funext t r j
      cases r <;> simp [Env.denote, Env.push, SpecEnv.push, BinaryOp.eval, BinaryOp.denote]
    exact congrArg (fun e : SpecEnv ℝ _ => next.differential e
      (df.push ((AD.differential op (env.denote left) (env.denote right)).comp
        ((df left).prod (df right)))) dx i) he

/-- The emitted ordinary tensor program computes a true mathematical
derivative. Entry registers may themselves be differentiable functions; the
statement covers the complete chain from their input to the final result. -/
theorem Program.forward_derivative (p : Program Γ s) (primal tangent : Ren Γ Δ)
    (env : Env ℝ Δ) (f : AD.Space input → SpecEnv ℝ Γ) (df : LinearEnv input Γ)
    (x dx : AD.Space input) (hreg : p.RegularAt (f x))
    (hf : ∀ {t} (r : Ref Γ t), HasFDerivAt (fun x => f x r) (df r) x)
    (hp : ∀ {t} (r : Ref Γ t) (i : Fin t.volume), (env (primal r))[i] = f x r i)
    (ht : ∀ {t} (r : Ref Γ t) (i : Fin t.volume), (env (tangent r))[i] = df r dx i) :
    ∃ derivative : AD.Space input →L[ℝ] AD.Space s,
      HasFDerivAt (fun x => p.denote AD.realOps 0 1 (f x)) derivative x ∧
      ∀ i, ((p.forward primal tangent .tangent).eval AD.realOps 0 1 env)[i] = derivative dx i := by
  refine ⟨p.differential (f x) df, p.hasFDerivAt f df x hreg hf, ?_⟩
  have hd := p.evalForward_tangent (fun r => env (primal r)) (fun r => env (tangent r)) df dx ht
  have he : (Env.denote (fun r => env (primal r)) : SpecEnv ℝ Γ) =
      (fun {t} (r : Ref Γ t) => f x r) := by
    funext t r i
    exact hp r i
  rw [he] at hd
  simpa only [forward_correct, Projection.select] using hd

end Rumoca.Solve.Tensor
