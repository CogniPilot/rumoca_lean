import RumocaCore.Tensor.Operators

/-! Compact tensor programs. Shapes are part of the type of every reference;
execution uses array-backed vectors. IR construction never enumerates tensor
coordinates. Arithmetic is pointwise; stencils and contractions require their
own subsequent contracts.
-/
namespace Rumoca.Solve.Tensor
open Rumoca.Tensor

/-- References preserve rank and all extents, not just element count. -/
inductive Ref : List Shape → Shape → Type where
  | here : Ref (s :: Γ) s
  | there : Ref Γ s → Ref (t :: Γ) s
  deriving Repr

abbrev Env (α : Type) (Γ : List Shape) := {s : Shape} → Ref Γ s → Value α s

def Env.empty : Env α [] := fun r => nomatch r

def Env.push (value : Value α s) (env : Env α Γ) : Env α (s :: Γ)
  | _, .here => value
  | _, .there r => env r

inductive Literal where
  | zero
  | one
  deriving Repr, BEq, DecidableEq

def Literal.eval (zero one : α) : Literal → α
  | .zero => zero
  | .one => one

/-- A fill creates one tensor register regardless of its volume. Future
operations belong here, rather than in an FMI adapter or a scalarized IR. -/
inductive Program : List Shape → Shape → Type where
  | ret : Ref Γ s → Program Γ s
  | fill (shape : Shape) (value : Literal) (next : Program (shape :: Γ) s) : Program Γ s
  | binary (op : BinaryOp) (left right : Ref Γ shape)
      (next : Program (shape :: Γ) s) : Program Γ s
  deriving Repr

def Program.eval (ops : ScalarOps α) (zero one : α) : Program Γ s → Env α Γ → Value α s
  | .ret r, env => env r
  | .fill shape value next, env =>
      next.eval ops zero one (env.push (Value.fill shape (value.eval zero one)))
  | .binary op left right next, env =>
      next.eval ops zero one (env.push (op.eval ops (env left) (env right)))

def Program.nodeCount : Program Γ s → Nat
  | .ret _ => 1
  | .fill _ _ next => next.nodeCount + 1
  | .binary _ _ _ next => next.nodeCount + 1

def fill (shape : Shape) (value : Literal) : Program Γ shape :=
  .fill shape value (.ret .here)

theorem fill_nodeCount (shape : Shape) (value : Literal) :
    (fill (Γ := Γ) shape value).nodeCount = 2 := rfl

/-- Mathematical tensor interpretation, independent of the array evaluator. -/
abbrev SpecEnv (α : Type) (Γ : List Shape) := {s : Shape} → Ref Γ s → Denotation α s

def SpecEnv.push (value : Denotation α s) (env : SpecEnv α Γ) : SpecEnv α (s :: Γ)
  | _, .here => value
  | _, .there r => env r

def Program.denote (ops : ScalarOps α) (zero one : α) : Program Γ s → SpecEnv α Γ → Denotation α s
  | .ret r, env => env r
  | .fill _ value next, env => next.denote ops zero one (env.push (fun _ => value.eval zero one))
  | .binary op left right next, env =>
      next.denote ops zero one (env.push (op.denote ops (env left) (env right)))

/-- The executable evaluator implements the tensor denotation at every valid
coordinate. The result holds for any rank, extent, literal interpretation and
well-typed program, including empty tensors and all input register values. -/
theorem Program.eval_correct (p : Program Γ s) (ops : ScalarOps α) (zero one : α) (env : Env α Γ) :
    ∀ i, (p.eval ops zero one env)[i] = p.denote ops zero one (fun r i => (env r)[i]) i := by
  induction p with
  | ret => intro i; rfl
  | fill shape value next ih =>
    intro i
    rw [Program.eval, ih]
    simp only [Program.denote]
    congr 1
    funext t r j
    cases r <;> simp [Env.push, SpecEnv.push]
  | binary op left right next ih =>
    intro i
    rw [Program.eval, ih]
    simp only [Program.denote]
    congr 1
    funext t r j
    cases r <;> simp [Env.push, SpecEnv.push, BinaryOp.eval, BinaryOp.denote]

end Rumoca.Solve.Tensor
