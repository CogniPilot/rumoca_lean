import RumocaCore.GALEC.Semantics
import RumocaCore.Solve.Tensor

/-! Executable Algorithm Code refinement. The numerical IVP and algorithm roots
are separate products. Production code consumes this root, never GALEC syntax
or a reconstructed DAE. Register references retain complete tensor shapes. -/
namespace Rumoca.Solve.Algorithm
open Rumoca.Tensor
open Rumoca.Solve.Tensor (Ref Env)

inductive Program : List Shape → Shape → Type where
  | ret : Ref Γ shape → Program Γ shape
  | fill (value : Solve.Tensor.Literal) (next : Program (shape :: Γ) result) : Program Γ result
  | add (left right : Ref Γ shape) (next : Program (shape :: Γ) result) : Program Γ result
  deriving Repr

def Program.eval (zero one : α) (add : α → α → α) :
    Program Γ shape → Env α Γ → Value α shape
  | .ret ref, env => env ref
  | .fill value next, env =>
      next.eval zero one add (env.push (Value.fill _ (value.eval zero one)))
  | .add left right next, env =>
      next.eval zero one add (env.push (GALEC.zipWith add (env left) (env right)))

/-- Continuation lowering emits a tensor instruction per source operation,
not one per coordinate. `state` is explicitly threaded as registers are added. -/
abbrev Ren (Γ Δ : List Shape) := {s : Shape} → Ref Γ s → Ref Δ s

def lowerExpr (expr : GALEC.Expr shape) (state : Ref Γ shape)
    (k : {Δ : List Shape} → Ren Γ Δ → Ref Δ shape → Program Δ result) : Program Γ result :=
  match expr with
  | .state => k (fun r => r) state
  | .zero => .fill .zero (k (fun r => .there r) .here)
  | .one => .fill .one (k (fun r => .there r) .here)
  | .add a b =>
      lowerExpr a state fun ren left =>
        lowerExpr b (ren state) fun ren' right =>
          .add (ren' left) right (k (fun r => .there (ren' (ren r))) .here)

def compileExpr (e : GALEC.Expr shape) : Program [shape] shape :=
  lowerExpr e .here (fun _ result => .ret result)

structure Block (shape : Shape) where
  startup : Program [shape] shape
  recalibrate : Program [shape] shape
  doStep : Program [shape] shape
  startupPeriod : Program [scalar] scalar
  deriving Repr

def compileBody : Option (GALEC.Expr shape) → Program [shape] shape
  | none => .ret .here
  | some e => compileExpr e

def lower (b : GALEC.Block shape) : Block shape :=
  ⟨compileBody b.startup, compileBody b.recalibrate, compileBody b.doStep,
    compileExpr b.startupPeriod⟩

def Block.body (b : Block shape) : GALEC.Method → Program [shape] shape
  | .startup => b.startup
  | .recalibrate => b.recalibrate
  | .doStep => b.doStep

def Block.execute (b : Block shape) (zero one : α) (add : α → α → α)
    (method : GALEC.Method) (state : Value α shape) : Value α shape :=
  (b.body method).eval zero one add (Env.push state Env.empty)

def Block.trace (b : Block shape) (zero one : α) (add : α → α → α)
    (state : Value α shape) : List GALEC.Method → Value α shape
  | [] => state
  | m :: ms => b.trace zero one add (b.execute zero one add m state) ms

/-- Prepared executable root with provenance. Backends read `block`; they do
not repeat GALEC refinement or inspect DAE equations to select a solver. -/
structure Model (source : AST.Model) where
  origin : GALEC.Model source
  block : Block scalar
  lowered : block = lower origin.block

def prepare (model : GALEC.Model source) : Model source := ⟨model, lower model.block, rfl⟩

theorem Model.block_is_unit (model : Model source) : model.block = lower GALEC.unitBlock := by
  rw [model.lowered, model.origin.profile]

end Rumoca.Solve.Algorithm
