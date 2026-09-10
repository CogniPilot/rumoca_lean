import RumocaCore.Solve.Tensor

/-! Forward AD on the typed tensor register program. The reference evaluator
propagates primal/tangent environments together. The transformation emits only
ordinary whole-tensor instructions, preserving register sharing and shape.
Neither path constructs a Jacobian or enumerates tensor coordinates. -/
namespace Rumoca.Solve.Tensor
open Rumoca.Tensor

abbrev Ren (Γ Δ : List Shape) := {s : Shape} → Ref Γ s → Ref Δ s

def Ren.empty : Ren [] Δ := fun r => nomatch r

def Ren.push (r : Ref Δ shape) (ren : Ren Γ Δ) : Ren (shape :: Γ) Δ
  | _, .here => r
  | _, .there r => ren r

def Program.evalForward (ops : ScalarOps α) (zero one : α) :
    Program Γ s → Env α Γ → Env α Γ → Value α s × Value α s
  | .ret r, env, tangent => (env r, tangent r)
  | .fill shape value next, env, tangent =>
      next.evalForward ops zero one
        (env.push (Value.fill shape (value.eval zero one)))
        (tangent.push (Value.fill shape zero))
  | .binary op left right next, env, tangent =>
      next.evalForward ops zero one (env.push (op.eval ops (env left) (env right)))
        (tangent.push (op.jvp ops (env left) (env right) (tangent left) (tangent right)))

theorem Program.evalForward_primal (p : Program Γ s) (ops : ScalarOps α) (zero one : α)
    (env tangent : Env α Γ) :
    (p.evalForward ops zero one env tangent).1 = p.eval ops zero one env := by
  induction p with
  | ret => rfl
  | fill shape value next ih => exact ih _ _
  | binary op left right next ih => exact ih _ _

inductive Projection where
  | primal
  | tangent
  deriving Repr, BEq, DecidableEq

def Projection.select (projection : Projection) (primal tangent : α) : α :=
  match projection with
  | .primal => primal
  | .tangent => tangent

/-- `primal` and `tangent` map source registers to their already computed
values in the destination. Each source operation is visited exactly once.
The two products of the multiplication rule retain their specified order. -/
def Program.forward (p : Program Γ s) (primal tangent : Ren Γ Δ)
    (projection : Projection) : Program Δ s :=
  match p with
  | .ret r => .ret (projection.select (primal r) (tangent r))
  | .fill shape value next =>
      .fill shape value (.fill shape .zero
        (next.forward
          (Ren.push (.there .here) (fun r => .there (.there (primal r))))
          (Ren.push .here (fun r => .there (.there (tangent r)))) projection))
  | .binary .add left right next =>
      .binary .add (primal left) (primal right)
        (.binary .add (.there (tangent left)) (.there (tangent right))
          (next.forward
            (Ren.push (.there .here) (fun r => .there (.there (primal r))))
            (Ren.push .here (fun r => .there (.there (tangent r)))) projection))
  | .binary .mul left right next =>
      .binary .mul (primal left) (primal right)
        (.binary .mul (.there (primal left)) (.there (tangent right))
          (.binary .mul (.there (.there (primal right))) (.there (.there (tangent left)))
            (.binary .add (.there .here) .here
              (next.forward
                (Ren.push (.there (.there (.there .here)))
                  (fun r => .there (.there (.there (.there (primal r))))))
                (Ren.push .here (fun r => .there (.there (.there (.there (tangent r))))))
                projection))))

/-- Translation is correct for arbitrary scalar operations, so it preserves
the exact expression ordering even when the chosen arithmetic is rounded. -/
theorem Program.forward_correct (p : Program Γ s) (ops : ScalarOps α) (zero one : α)
    (primal tangent : Ren Γ Δ) (env : Env α Δ) (projection : Projection) :
    (p.forward primal tangent projection).eval ops zero one env =
      projection.select (p.evalForward ops zero one (fun r => env (primal r))
        (fun r => env (tangent r))).1
        (p.evalForward ops zero one (fun r => env (primal r))
          (fun r => env (tangent r))).2 := by
  induction p generalizing Δ with
  | ret r => cases projection <;> rfl
  | fill shape value next ih =>
    simp only [forward, eval, ih, evalForward]
    congr 3 <;> funext t r <;> cases r <;> rfl
  | binary op left right next ih =>
    cases op <;> simp only [forward, eval, ih, evalForward]
    all_goals congr 3 <;> funext t r <;> cases r <;> rfl

theorem Program.forward_primal (p : Program Γ s) (ops : ScalarOps α) (zero one : α)
    (primal tangent : Ren Γ Δ) (env : Env α Δ) :
    (p.forward primal tangent .primal).eval ops zero one env =
      p.eval ops zero one (fun r => env (primal r)) := by
  rw [forward_correct]
  exact p.evalForward_primal ops zero one _ _

/-- A constant instruction-count bound, independent of every tensor extent. -/
theorem Program.forward_compact (p : Program Γ s) (primal tangent : Ren Γ Δ)
    (projection : Projection) :
    (p.forward primal tangent projection).nodeCount ≤ 4 * p.nodeCount := by
  induction p generalizing Δ with
  | ret => simp [forward, nodeCount]
  | fill shape value next ih =>
    simp only [forward, nodeCount]
    have h := ih (Δ := shape :: shape :: Δ) (Ren.push (.there .here) (fun r => .there (.there (primal r))))
      (Ren.push .here (fun r => .there (.there (tangent r))))
    omega
  | @binary Γ shape s op left right next ih =>
    cases op <;> simp only [forward, nodeCount]
    · have h := ih (Δ := shape :: shape :: Δ) (Ren.push (.there .here) (fun r => .there (.there (primal r))))
        (Ren.push .here (fun r => .there (.there (tangent r))))
      omega
    · have h := ih (Δ := shape :: shape :: shape :: shape :: Δ) (Ren.push (.there (.there (.there .here)))
          (fun r => .there (.there (.there (.there (primal r))))))
        (Ren.push .here (fun r => .there (.there (.there (.there (tangent r))))))
      omega

end Rumoca.Solve.Tensor
