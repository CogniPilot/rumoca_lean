import ModelicaParser.Array.Syntax
import RumocaCore.Tensor.Operators

/-! Indexed declarative IRs for the fixed array profile. Resolution removes
names from expressions; state, input and derivative remain distinct roles.
Jacobian equations retain an expression to differentiate, rather than a
candidate matrix or a per-coordinate list of scalar equations. -/
namespace Rumoca.ArrayProfile
open Rumoca.Tensor

def stateShape : Shape := ⟨[2]⟩
def jacobianShape : Shape := ⟨[2, 2]⟩

theorem Model.state_shape (m : Model) : stateShape.dimensions = m.stateDimensions := rfl
theorem Model.jacobian_shape (m : Model) : jacobianShape.dimensions = m.jacobianDimensions := rfl

namespace Flat

inductive Expr (shape : Shape) where
  | input
  | state
  | zero
  | binary (op : BinaryOp) (left right : Expr shape)
  deriving Repr, BEq, DecidableEq

def rhsFor (body : Body) : Expr shape :=
  match body with
  | .driven .. => .input
  | .jacobian .. => .binary .mul .input .input

/-- All calls in this profile differentiate with respect to the input tensor.
That restriction is checked by source resolution, not by a backend. -/
def jacobianFor (body : Body) : Option (Expr shape) :=
  match body with
  | .driven .. => none
  | .jacobian .. => some (.binary .mul .input .input)

structure Model (source : ArrayProfile.Model) where
  resolved : source.Resolved
  rhs : Expr stateShape
  initial : Expr stateShape
  jacobian : Option (Expr stateShape)
  rhs_source : rhs = rhsFor source.body
  initial_source : initial = .zero
  jacobian_source : jacobian = jacobianFor source.body

def lower (source : ArrayProfile.Model) (resolved : source.Resolved) : Model source :=
  ⟨resolved, rhsFor source.body, .zero, jacobianFor source.body, rfl, rfl, rfl⟩

end Flat

namespace DAE

inductive Expr (shape : Shape) where
  | input
  | state
  | derivative
  | zero
  | binary (op : BinaryOp) (left right : Expr shape)
  | sub (left right : Expr shape)
  deriving Repr, BEq, DecidableEq

def lowerExpr : Flat.Expr shape → Expr shape
  | .input => .input
  | .state => .state
  | .zero => .zero
  | .binary op left right => .binary op (lowerExpr left) (lowerExpr right)

/-- Residuals specify both the continuous equation and fixed initialization.
The Jacobian equation still denotes differentiation with respect to input;
choosing an executable derivative algorithm belongs to Solve lowering. -/
structure Model (source : ArrayProfile.Model) where
  flat : Flat.Model source
  residual : Expr stateShape
  initialResidual : Expr stateShape
  jacobian : Option (Expr stateShape)
  residual_source : residual = .sub .derivative (lowerExpr flat.rhs)
  initial_source : initialResidual = .sub .state (lowerExpr flat.initial)
  jacobian_source : jacobian = flat.jacobian.map lowerExpr

def lower (flat : Flat.Model source) : Model source :=
  ⟨flat, .sub .derivative (lowerExpr flat.rhs), .sub .state (lowerExpr flat.initial),
    flat.jacobian.map lowerExpr, rfl, rfl, rfl⟩

end DAE
end Rumoca.ArrayProfile
