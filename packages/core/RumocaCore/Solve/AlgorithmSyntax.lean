import RumocaCore.GALEC.Method
import RumocaCore.Solve.Tensor

/-! The prepared executable Algorithm Code. The numerical IVP and algorithm roots
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
      next.eval zero one add (env.push ((env left).zipWith add (env right)))

/-- One register program per lifecycle method; `startupPeriod` initializes the
immutable sampling-period constant after the Startup state program. -/
structure Block (shape : Shape) where
  startup : Program [shape] shape
  recalibrate : Program [shape] shape
  doStep : Program [shape] shape
  startupPeriod : Program [scalar] scalar
  deriving Repr

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

/-- The unit-step, zero-start profile: Startup fills zero, Recalibrate returns
the state, DoStep adds the filled one to the state, and the period is one. -/
def unitBlock : Block scalar :=
  ⟨.fill .zero (.ret .here), .ret .here, .fill .one (.add (.there .here) .here (.ret .here)),
    .fill .one (.ret .here)⟩

end Rumoca.Solve.Algorithm
