import RumocaCore.Array.IR
import RumocaCore.Array.Builtin

/-! Independent source, Flat and DAE equations for the two-wide array profile.
The Jacobian equation specifies a true Fréchet derivative, not the diagonal
formula that a later lowering may choose. Source names and declared shapes
are bound at the first edge; all subsequent expressions use indexed roles. -/
noncomputable section
namespace Rumoca.ArrayProfile
open Rumoca.Tensor

abbrev Jacobian (shape : Shape) := Matrix (Fin shape.volume) (Fin shape.volume) ℝ

def JacobianOf (f : AD.Space shape → AD.Space shape) (input : AD.Space shape)
    (matrix : Jacobian shape) : Prop :=
  ∃ derivative : AD.Space shape →L[ℝ] AD.Space shape,
    HasFDerivAt f derivative input ∧ ∀ tangent, matrix.mulVec tangent = derivative tangent

def Model.Equation (m : Model) (values derivatives : Environment stateShape)
    (matrices : String → Jacobian stateShape) : Prop :=
  match m.body with
  | .driven derivative rhs => derivatives derivative = values rhs
  | .jacobian _ derivative rhs assigned call =>
      derivatives derivative = rhs.denote values ∧ call.Denotes values (matrices assigned)

def Model.Initial (m : Model) (values : Environment stateShape) : Prop :=
  values m.header.state = fun _ => 0

/-- The named observation on the source side of resolution. The driven
profile has no matrix observation, so its supplied value is immaterial. -/
def Model.jacobianValue (m : Model) (matrices : String → Jacobian stateShape) : Jacobian stateShape :=
  match m.body with
  | .driven .. => 0
  | .jacobian output .. => matrices output

def Flat.Expr.denote (state input : AD.Space shape) : Flat.Expr shape → AD.Space shape
  | .input => input
  | .state => state
  | .zero => fun _ => 0
  | .binary op left right => op.denote AD.realOps (left.denote state input) (right.denote state input)

def Flat.Model.Equation (m : Flat.Model source) (state input derivative : AD.Space stateShape)
    (matrix : Jacobian stateShape) : Prop :=
  derivative = m.rhs.denote state input ∧
    match m.jacobian with
    | none => True
    | some expr => JacobianOf (fun value => expr.denote state value) input matrix

def Flat.Model.Initial (m : Flat.Model source) (state input : AD.Space stateShape) : Prop :=
  state = m.initial.denote state input

theorem Call.square_denotes_iff (call : Call) (h : call.IsSquareOf input)
    (env : Environment shape) (matrix : Jacobian shape) :
    call.Denotes env matrix ↔
      JacobianOf (fun x => BinaryOp.denote AD.realOps .mul x x) (env input) matrix := by
  simp only [Call.Denotes, call.square_argument h, h.1, h.2.2.2, true_and, JacobianOf]

/-- Names disappear only after the source resolution evidence fixes every
operand and the differentiated variable. The Jacobian matrix remains arbitrary. -/
theorem Flat.lower_correct (m : ArrayProfile.Model) (resolved : m.Resolved)
    (values derivatives : Environment stateShape) (matrices : String → Jacobian stateShape) :
    m.Equation values derivatives matrices ↔
      (lower m resolved).Equation (values m.header.state) (values m.header.input)
        (derivatives m.header.state) (m.jacobianValue matrices) := by
  obtain ⟨header, body, endName⟩ := m
  cases body with
  | driven derivative rhs =>
    obtain ⟨_, _, _, _, hd, hr⟩ := resolved
    simp only [ArrayProfile.Model.Equation, Model.Equation, lower, rhsFor, jacobianFor,
      Expr.denote, and_true, hd, hr]
  | jacobian output derivative rhs assigned call =>
    obtain ⟨_, _, _, _, _, _, hd, hl, hr, ha, hb, hcl, hcr, hw⟩ := resolved
    have hp : rhs.denote values =
        BinaryOp.denote AD.realOps .mul (values header.input) (values header.input) := by
      funext i
      simp [Product.denote, hl, hr, BinaryOp.denote, BinaryOp.scalar, AD.realOps]
    change (derivatives derivative = rhs.denote values ∧ call.Denotes values (matrices assigned)) ↔
      derivatives header.state = BinaryOp.denote AD.realOps .mul (values header.input) (values header.input) ∧
        JacobianOf (fun x => BinaryOp.denote AD.realOps .mul x x) (values header.input) (matrices output)
    rw [hd, ha, hp]
    exact and_congr Iff.rfl (call.square_denotes_iff ⟨hb, hcl, hcr, hw⟩ values (matrices output))

theorem Flat.lower_initial (m : ArrayProfile.Model) (resolved : m.Resolved)
    (values : Environment stateShape) :
    m.Initial values ↔ (lower m resolved).Initial (values m.header.state) (values m.header.input) :=
  Iff.rfl

def DAE.Expr.denote (state input derivative : AD.Space shape) : DAE.Expr shape → AD.Space shape
  | .input => input
  | .state => state
  | .derivative => derivative
  | .zero => fun _ => 0
  | .binary op left right =>
      op.denote AD.realOps (left.denote state input derivative) (right.denote state input derivative)
  | .sub left right => fun i => left.denote state input derivative i - right.denote state input derivative i

theorem DAE.lowerExpr_correct (expr : Flat.Expr shape) (state input derivative : AD.Space shape) :
    (lowerExpr expr).denote state input derivative = expr.denote state input := by
  induction expr with
  | input => rfl
  | state => rfl
  | zero => rfl
  | binary op left right ihl ihr => simp only [lowerExpr, Expr.denote, Flat.Expr.denote, ihl, ihr]

def DAE.Model.Equation (m : DAE.Model source) (state input derivative : AD.Space stateShape)
    (matrix : Jacobian stateShape) : Prop :=
  (∀ i, m.residual.denote state input derivative i = 0) ∧
    match m.jacobian with
    | none => True
    | some expr => JacobianOf (fun value => expr.denote state value derivative) input matrix

def DAE.Model.Initial (m : DAE.Model source) (state input derivative : AD.Space stateShape) : Prop :=
  ∀ i, m.initialResidual.denote state input derivative i = 0

/-- This preserves the complete equation system, including the independently
specified Jacobian observation, rather than proving just its differential RHS. -/
theorem DAE.lower_correct (m : Flat.Model source) (state input derivative : AD.Space stateShape)
    (matrix : Jacobian stateShape) :
    m.Equation state input derivative matrix ↔ (lower m).Equation state input derivative matrix := by
  cases hj : m.jacobian <;>
    simp [Flat.Model.Equation, Model.Equation, lower, Expr.denote, lowerExpr_correct, hj,
      sub_eq_zero, funext_iff]

theorem DAE.lower_initial (m : Flat.Model source) (state input derivative : AD.Space stateShape) :
    m.Initial state input ↔ (lower m).Initial state input derivative := by
  simp [Flat.Model.Initial, Model.Initial, lower, Expr.denote, lowerExpr_correct, sub_eq_zero, funext_iff]

theorem dae_chain_correct (m : Model) (resolved : m.Resolved)
    (values derivatives : Environment stateShape) (matrices : String → Jacobian stateShape) :
    m.Equation values derivatives matrices ↔
      (DAE.lower (Flat.lower m resolved)).Equation (values m.header.state) (values m.header.input)
        (derivatives m.header.state) (m.jacobianValue matrices) :=
  (Flat.lower_correct m resolved values derivatives matrices).trans (DAE.lower_correct _ _ _ _ _)

theorem dae_initialization_correct (m : Model) (resolved : m.Resolved)
    (values derivatives : Environment stateShape) :
    m.Initial values ↔
      (DAE.lower (Flat.lower m resolved)).Initial (values m.header.state) (values m.header.input)
        (derivatives m.header.state) :=
  (Flat.lower_initial m resolved values).trans (DAE.lower_initial _ _ _ _)

end Rumoca.ArrayProfile
