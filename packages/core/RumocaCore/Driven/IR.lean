import ModelicaParser.Driven
import RumocaCore.Solve.ModelData

open _root_.Parser

/-! Source-indexed lowering for the driven scalar profile. Scalar variables
are rank-zero tensors from the first indexed stage onward. No equation or
instruction is generated per tensor coordinate. -/
namespace Rumoca.Driven
open Rumoca.Tensor Solve.Tensor

namespace Flat

inductive Expr (shape : Shape) where
  | der
  | input
  | state
  | zero
  deriving Repr, BEq, DecidableEq

def Expr.eval (zero : α) (state input derivative : Value α shape) : Expr shape → Value α shape
  | .der => derivative
  | .input => input
  | .state => state
  | .zero => Value.fill shape zero

structure Model (source : Driven.Model) where
  resolved : Resolved source
  lhs : Expr scalar
  rhs : Expr scalar
  initialLhs : Expr scalar
  initialRhs : Expr scalar
  lhs_source : lhs = .der
  rhs_source : rhs = .input
  initialLhs_source : initialLhs = .state
  initialRhs_source : initialRhs = .zero

def lower (source : Driven.Model) (h : Resolved source) : Model source :=
  ⟨h, .der, .input, .state, .zero, rfl, rfl, rfl, rfl⟩

end Flat

namespace DAE

inductive Expr (shape : Shape) where
  | derivative
  | input
  | state
  | zero
  | sub (left right : Expr shape)
  deriving Repr, BEq, DecidableEq

def lowerExpr : Flat.Expr shape → Expr shape
  | .der => .derivative
  | .input => .input
  | .state => .state
  | .zero => .zero

structure Model (source : Driven.Model) where
  flat : Flat.Model source
  residual : Expr scalar
  initialResidual : Expr scalar
  residual_source : residual = .sub (lowerExpr flat.lhs) (lowerExpr flat.rhs)
  initialResidual_source : initialResidual = .sub (lowerExpr flat.initialLhs) (lowerExpr flat.initialRhs)

def lower (flat : Flat.Model source) : Model source :=
  ⟨flat, .sub (lowerExpr flat.lhs) (lowerExpr flat.rhs),
    .sub (lowerExpr flat.initialLhs) (lowerExpr flat.initialRhs), rfl, rfl⟩

end DAE

namespace Solved

/-- Source evidence is separate from the executable IVP. A backend receives
`ivp`; it does not need to inspect the AST or redo any lowering. -/
structure Model (source : Driven.Model) where
  dae : DAE.Model source
  ivp : Solve.IVP
  ivp_source : ivp = Solve.drivenIVP scalar

def lower (dae : DAE.Model source) : Model source :=
  ⟨dae, Solve.drivenIVP scalar, rfl⟩

/-- A correlated read-only export root; all names and shapes come from this
model's own lowering chain. FMI must project this root, not re-read the AST. -/
def Model.exportData (m : Model source) : Solve.ModelData where
  problem := m.ivp
  output_shape := by rw [m.ivp_source]; rfl
  output_is_state := by rw [m.ivp_source]; rfl
  stateName := source.state
  inputName := source.input
  distinct := Ne.symm m.dae.flat.resolved.2.2.2.1

theorem Model.export_problem (m : Model source) : m.exportData.problem = m.ivp := rfl

theorem Model.export_state_name (m : Model source) :
    m.exportData.name .state = source.state := rfl

theorem Model.export_input_name (m : Model source) :
    m.exportData.name .input = source.input := rfl

end Solved
end Rumoca.Driven
