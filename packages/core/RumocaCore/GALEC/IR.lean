import RumocaCore.Tensor
import RumocaCore.IR

/-! A checked Algorithm Code product of DAE. This is not another residual IR
and is not inserted into the numerical IVP path. The initial profile has one
rank-zero state, unit sampling period and explicit lifecycle assignments. -/
namespace Rumoca.GALEC
open Rumoca.Tensor

inductive Method where
  | startup | recalibrate | doStep
  deriving Repr, BEq, DecidableEq

/-- Every expression retains its entire tensor shape. -/
inductive Expr (shape : Shape) where
  | state
  | zero
  | one
  | add (left right : Expr shape)
  deriving Repr, BEq, DecidableEq

/-- `none` denotes an empty method; `some e` assigns the state to `e`.
No general statement language is admitted by this first product. -/
structure Block (shape : Shape) where
  startup : Option (Expr shape)
  recalibrate : Option (Expr shape)
  doStep : Option (Expr shape)
  /-- The clock constant is initialized by Startup, after the state assignment.
  It is explicit in this product so a backend cannot choose its value. -/
  startupPeriod : Expr scalar
  deriving Repr, BEq, DecidableEq

def Block.body (b : Block shape) : Method → Option (Expr shape)
  | .startup => b.startup
  | .recalibrate => b.recalibrate
  | .doStep => b.doStep

def unitBlock : Block scalar := ⟨some .zero, none, some (.add .state .one), .one⟩

/-- This admission token binds the Algorithm Code to its original DAE and to
the explicit unit-step/zero-start profile. It does not license arbitrary DAEs. -/
structure Model (source : AST.Model) where
  dae : DAE.Model source
  block : Block scalar
  profile : block = unitBlock

def lower (dae : DAE.Model source) : Model source := ⟨dae, unitBlock, rfl⟩

end Rumoca.GALEC
