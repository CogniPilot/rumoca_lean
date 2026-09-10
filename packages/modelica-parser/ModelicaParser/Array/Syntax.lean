import Parser.Token

/-! Syntax for the first array/AD profile. A product is one tensor operation;
its operands are source names. Calls retain their name and arguments, so the
parser does not confuse recognizing call syntax with resolving an intrinsic.
No core IR or differentiation implementation is imported by this frontend. -/
namespace Rumoca.ArrayProfile

open _root_.Parser

structure Product where
  left : String
  right : String
  deriving Repr, BEq, DecidableEq

def Product.tokens (p : Product) : List Token :=
  [.ident p.left, .literal ".*", .ident p.right]

/-- Only the argument form needed by the first Jacobian is admitted. -/
structure Call where
  name : String
  expression : Product
  wrt : String
  deriving Repr, BEq, DecidableEq

inductive Builtin where
  | jacobian
  deriving Repr, BEq, DecidableEq

def Call.builtin? (c : Call) : Option Builtin :=
  if c.name = "jacobian" then some .jacobian else none

theorem Call.jacobian_iff (c : Call) : c.builtin? = some .jacobian ↔ c.name = "jacobian" := by
  simp [builtin?]

def Call.tokens (c : Call) : List Token :=
  [.ident c.name, .literal "("] ++ c.expression.tokens ++
    [.literal ",", .ident c.wrt, .literal ")"]

structure Header where
  name : String
  input : String
  state : String
  startAttribute : String
  fixedAttribute : String
  deriving Repr, BEq, DecidableEq

inductive Body where
  | driven (derivative rhs : String)
  | jacobian (output derivative : String) (rhs : Product) (assigned : String) (call : Call)
  deriving Repr, BEq, DecidableEq

structure Model where
  header : Header
  body : Body
  endName : String
  deriving Repr, BEq, DecidableEq

/-- Static extents belong to this syntax profile; no elements are enumerated. -/
def Model.stateDimensions (_ : Model) : List Nat := [2]

def Model.jacobianDimensions (_ : Model) : List Nat := [2, 2]

def Header.tokens (h : Header) : List Token :=
  [.literal "model", .ident h.name,
   .literal "input", .literal "Real", .ident h.input,
   .literal "[", .literal "2", .literal "]", .literal ";",
   .literal "output", .literal "Real", .ident h.state,
   .literal "[", .literal "2", .literal "]", .literal "(",
   .literal "each", .ident h.startAttribute, .literal "=", .literal "0", .literal ",",
   .literal "each", .ident h.fixedAttribute, .literal "=", .literal "true", .literal ")",
   .literal ";"]

def Body.tokens : Body → List Token
  | .driven derivative rhs =>
    [.literal "equation", .literal "der", .literal "(", .ident derivative,
     .literal ")", .literal "=", .ident rhs, .literal ";"]
  | .jacobian output derivative rhs assigned call =>
    [.literal "output", .literal "Real", .ident output, .literal "[", .literal "2",
     .literal ",", .literal "2", .literal "]", .literal ";",
     .literal "equation", .literal "der", .literal "(", .ident derivative,
     .literal ")", .literal "="] ++ rhs.tokens ++
    [.literal ";", .ident assigned, .literal "="] ++ call.tokens ++ [.literal ";"]

def Model.tokens (m : Model) : List Token :=
  m.header.tokens ++ m.body.tokens ++ [.literal "end", .ident m.endName, .literal ";"]

/-- This semantic restriction selects the existing proved square operator.
Parsing also retains other names, allowing resolution to report their ranges. -/
def Model.Resolved (m : Model) : Prop :=
  m.endName = m.header.name ∧ m.header.input ≠ m.header.state ∧
  m.header.startAttribute = "start" ∧ m.header.fixedAttribute = "fixed" ∧
  match m.body with
  | .driven derivative rhs => derivative = m.header.state ∧ rhs = m.header.input
  | .jacobian output derivative rhs assigned call =>
    output ≠ m.header.input ∧ output ≠ m.header.state ∧
    derivative = m.header.state ∧ rhs.left = m.header.input ∧ rhs.right = m.header.input ∧
    assigned = output ∧ call.builtin? = some .jacobian ∧
    call.expression.left = m.header.input ∧ call.expression.right = m.header.input ∧
    call.wrt = m.header.input

instance (m : Model) : Decidable m.Resolved := by
  unfold Model.Resolved
  cases m.body <;> infer_instance

end Rumoca.ArrayProfile
