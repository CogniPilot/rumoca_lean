import RumocaCore.GALEC.IR

/-! Independent expression and lifecycle semantics for the admitted Algorithm
Code. Arithmetic is a parameter; the binary64 profile is one interpretation,
not a claim that eFMI universally mandates binary64. -/
namespace Rumoca.GALEC
open Rumoca.Tensor

def zipWith (f : α → α → α) (x y : Value α shape) : Value α shape :=
  ⟨x.data.zipWith f y.data⟩

@[simp] theorem get_zipWith (f : α → α → α) (x y : Value α shape)
    (h : i < shape.volume) : (zipWith f x y)[i] = f x[i] y[i] := by
  change (Vector.zipWith f x.data y.data)[i] = f x.data[i] y.data[i]
  exact Vector.getElem_zipWith h

def Expr.eval (zero one : α) (add : α → α → α) (state : Value α shape) :
    Expr shape → Value α shape
  | .state => state
  | .zero => Value.fill shape zero
  | .one => Value.fill shape one
  | .add a b => zipWith add (a.eval zero one add state) (b.eval zero one add state)

def Block.execute (b : Block shape) (zero one : α) (add : α → α → α)
    (method : Method) (state : Value α shape) : Value α shape :=
  match b.body method with
  | none => state
  | some expr => expr.eval zero one add state

def Block.trace (b : Block shape) (zero one : α) (add : α → α → α)
    (state : Value α shape) : List Method → Value α shape
  | [] => state
  | m :: ms => b.trace zero one add (b.execute zero one add m state) ms

/-- Separate relational execution specification, including the empty method. -/
inductive Executes (zero one : α) (add : α → α → α) :
    Option (Expr shape) → Value α shape → Value α shape → Prop where
  | skip (state) : Executes zero one add none state state
  | assign (expr state) : Executes zero one add (some expr) state (expr.eval zero one add state)

theorem execute_correct (b : Block shape) (zero one : α) (add : α → α → α)
    (method : Method) (state result : Value α shape) :
    Executes zero one add (b.body method) state result ↔
      result = b.execute zero one add method state := by
  cases h : b.body method <;> simp only [Block.execute, h]
  · constructor
    · intro e; cases e; rfl
    · rintro rfl; exact .skip _
  · constructor
    · intro e; cases e; rfl
    · rintro rfl; exact .assign _ _

end Rumoca.GALEC
