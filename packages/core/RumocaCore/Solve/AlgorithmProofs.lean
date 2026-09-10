import RumocaCore.Solve.Algorithm

namespace Rumoca.Solve.Algorithm
open Rumoca.Tensor
open Rumoca.Solve.Tensor (Ref Env)

/-- Continuation compilation preserves old registers and the expression value.
This quantifies over every rank, extent and arithmetic interpretation. -/
theorem lowerExpr_correct (e : GALEC.Expr shape) (zero one : α) (add : α → α → α)
    (state : Ref Γ shape)
    (k : {Δ : List Shape} → Ren Γ Δ → Ref Δ shape → Program Δ result)
    (env : Env α Γ) (output : Value α result)
    (hk : ∀ {Δ} (ren : Ren Γ Δ) (ref : Ref Δ shape) (env' : Env α Δ),
      (∀ {s} (r : Ref Γ s), env' (ren r) = env r) →
      env' ref = e.eval zero one add (env state) →
      (k ren ref).eval zero one add env' = output) :
    (lowerExpr e state k).eval zero one add env = output := by
  induction e generalizing Γ with
  | state => exact hk (fun r => r) state env (fun _ => rfl) rfl
  | zero =>
    exact hk (fun r => .there r) .here (env.push (Value.fill _ zero)) (fun _ => rfl) rfl
  | one =>
    exact hk (fun r => .there r) .here (env.push (Value.fill _ one)) (fun _ => rfl) rfl
  | add a b ia ib =>
    simp only [lowerExpr]
    apply ia
    intro Δ ren left envA preservedA valueA
    apply ib
    intro Δ' ren' right envB preservedB valueB
    apply hk (fun r => .there (ren' (ren r))) .here
      (envB.push (GALEC.zipWith add (envB (ren' left)) (envB right)))
    · intro s r
      exact (preservedB (ren r)).trans (preservedA r)
    · change GALEC.zipWith add (envB (ren' left)) (envB right) = _
      rw [preservedB left, valueA, valueB, preservedA state]
      rfl

theorem compileExpr_correct (e : GALEC.Expr shape) (zero one : α)
    (add : α → α → α) (state : Value α shape) :
    (compileExpr e).eval zero one add (Env.push state Env.empty) =
      e.eval zero one add state := by
  apply lowerExpr_correct
  intro Δ ren ref env preserved value
  exact value

theorem compileBody_correct (body : Option (GALEC.Expr shape)) (zero one : α)
    (add : α → α → α) (state : Value α shape) :
    (compileBody body).eval zero one add (Env.push state Env.empty) =
      (match body with | none => state | some e => e.eval zero one add state) := by
  cases body with
  | none => rfl
  | some e => exact compileExpr_correct e zero one add state

/-- GALEC → Solve preserves every lifecycle method's complete state result. -/
theorem lower_correct (b : GALEC.Block shape) (zero one : α) (add : α → α → α)
    (method : GALEC.Method) (state : Value α shape) :
    (lower b).execute zero one add method state = b.execute zero one add method state := by
  have h := compileBody_correct (b.body method) zero one add state
  cases method <;>
    simpa [Block.execute, Block.body, lower, GALEC.Block.execute, GALEC.Block.body]
      using h

theorem lower_trace_correct (b : GALEC.Block shape) (zero one : α) (add : α → α → α)
    (state : Value α shape) (methods : List GALEC.Method) :
    (lower b).trace zero one add state methods = b.trace zero one add state methods := by
  induction methods generalizing state with
  | nil => rfl
  | cons m ms ih => simp only [Block.trace, GALEC.Block.trace, lower_correct, ih]

end Rumoca.Solve.Algorithm
