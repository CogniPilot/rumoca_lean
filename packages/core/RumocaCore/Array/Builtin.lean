import ModelicaParser.Array.Syntax
import RumocaCore.Tensor.Differentiation

/-! Mathematical semantics of the parsed Jacobian extension. Only the selected
variable changes during differentiation; all other names retain their values.
The specification asks for a true Fréchet derivative and its matrix action,
independently of the AD rule that produces the candidate diagonal matrix.
These are Real semantics, not derivatives of rounded floating-point execution. -/
noncomputable section
namespace Rumoca.ArrayProfile

open Rumoca.Tensor

abbrev Environment (s : Shape) := String → AD.Space s

def Product.denote (p : Product) (env : Environment s) : AD.Space s :=
  fun i => env p.left i * env p.right i

def Call.argumentFunction (call : Call) (env : Environment s) : AD.Space s → AD.Space s :=
  fun input => call.expression.denote (Function.update env call.wrt input)

/-- A Jacobian denotes the derivative's complete action on arbitrary tangents.
The existence obligation excludes nondifferentiable expressions, rather than
using mathlib's default value for `fderiv` at such a point. -/
def Call.Denotes (call : Call) (env : Environment s)
    (matrix : Matrix (Fin s.volume) (Fin s.volume) ℝ) : Prop :=
  call.builtin? = some .jacobian ∧
  ∃ derivative : AD.Space s →L[ℝ] AD.Space s,
    HasFDerivAt (call.argumentFunction env) derivative (env call.wrt) ∧
    ∀ tangent, matrix.mulVec tangent = derivative tangent

theorem Call.denotes_unique (call : Call) (env : Environment s)
    (h₁ : call.Denotes env a) (h₂ : call.Denotes env b) : a = b := by
  obtain ⟨_, da, ha, hma⟩ := h₁
  obtain ⟨_, db, hb, hmb⟩ := h₂
  have hd := ha.unique hb
  apply Matrix.mulVec_injective
  funext tangent
  rw [hma, hmb, hd]

def Call.IsSquareOf (call : Call) (input : String) : Prop :=
  call.builtin? = some .jacobian ∧ call.expression.left = input ∧
  call.expression.right = input ∧ call.wrt = input

theorem Call.square_argument (call : Call) (h : call.IsSquareOf input) (env : Environment s) :
    call.argumentFunction env = fun x => BinaryOp.denote AD.realOps .mul x x := by
  funext x i
  simp [argumentFunction, Product.denote, h.2.1, h.2.2.1, h.2.2.2,
    BinaryOp.denote, BinaryOp.scalar, AD.realOps]

/-- The diagonal AD result satisfies the independently specified source
built-in for every shape and environment, not just the two-wide example. -/
theorem Call.square_correct (call : Call) (h : call.IsSquareOf input) (env : Environment s) :
    call.Denotes env (AD.squareJacobian (env input)) := by
  refine ⟨h.1, AD.squareDifferential (env input), ?_, ?_⟩
  · rw [call.square_argument h env, h.2.2.2]
    exact AD.square_hasFDerivAt (env input)
  · exact AD.square_jacobian_correct (env input)

/-- This connects the actual resolved AST call to the AD rule. It does not
assert a source-to-C or whole-program AD compilation theorem. -/
theorem Model.jacobian_call_correct (m : Model) (resolved : m.Resolved)
    (body : m.body = .jacobian output derivative rhs assigned call) (env : Environment s) :
    call.Denotes env (AD.squareJacobian (env m.header.input)) := by
  obtain ⟨_, _, _, _, h⟩ := resolved
  rw [body] at h
  obtain ⟨_, _, _, _, _, _, builtin, left, right, wrt⟩ := h
  exact call.square_correct ⟨builtin, left, right, wrt⟩ env

end Rumoca.ArrayProfile
