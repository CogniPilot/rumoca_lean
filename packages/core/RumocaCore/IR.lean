import ModelicaParser.AST

open _root_.Parser

/-! Independent, deliberately small representations of the admitted profile.
No solver, target format, or machine bound appears in the semantic IRs. -/
namespace Rumoca

namespace Flat

/-- There is exactly one declared continuous Real state. Fin 1 rules out a
dangling derivative reference without a post-hoc root validator. -/
inductive Expr where
  | der (state : Fin 1)
  | one
  deriving Repr, BEq, DecidableEq

structure Model (source : AST.Model) where
  resolved : AST.Resolved source
  lhs : Expr
  rhs : Expr
  lhs_source : lhs = .der 0
  rhs_source : rhs = .one

def lower (source : AST.Model) (h : AST.Resolved source) : Model source :=
  ⟨h, .der 0, .one, rfl, rfl⟩

end Flat

namespace DAE

/-- Appendix B coordinates replace source temporal syntax. -/
inductive Expr where
  | derivative (slot : Fin 1)
  | one
  | sub (left right : Expr)
  deriving Repr, BEq, DecidableEq

def lowerExpr : Flat.Expr → Expr
  | .der s => .derivative s
  | .one => .one

structure Model (source : AST.Model) where
  flat : Flat.Model source
  residual : Expr
  residual_source : residual = .sub (lowerExpr flat.lhs) (lowerExpr flat.rhs)

def lower (flat : Flat.Model source) : Model source :=
  ⟨flat, .sub (lowerExpr flat.lhs) (lowerExpr flat.rhs), rfl⟩

end DAE

namespace Solve

/-- Straight-line register code. A return can only read an existing register.
This first instruction vocabulary contains the sole admitted constant. -/
inductive Program : Nat → Type where
  | ret (register : Fin n) : Program n
  | one (next : Program (n + 1)) : Program n
  deriving Repr

def evalWith (one : α) (p : Program n) (registers : Fin n → α) : α :=
  match p with
  | .ret r => registers r
  | .one next => evalWith one next (fun i => if h : i.val < n then registers ⟨i.val, h⟩ else one)

def eval (p : Program n) (registers : Fin n → Nat) : Nat := evalWith 1 p registers

def unitDerivative : Program 0 := .one (.ret 0)

structure Model (source : AST.Model) where
  dae : DAE.Model source
  derivative : Program 0
  derivative_source : derivative = unitDerivative

def lower (dae : DAE.Model source) : Model source :=
  ⟨dae, unitDerivative, rfl⟩

def Model.rhs (m : Model source) : Nat := eval m.derivative Fin.elim0

theorem Model.rhs_eq_one (m : Model source) : m.rhs = 1 := by
  simp [Model.rhs, m.derivative_source, unitDerivative, eval, evalWith]

end Solve
end Rumoca
