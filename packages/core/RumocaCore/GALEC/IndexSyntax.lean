import RumocaCore.Tensor.Coordinates

/-! Intrinsic iterator and per-axis index syntax. No functions are
stored in the syntax, and it has no source names or mutable iterator writes. -/
namespace Rumoca.GALEC
open Rumoca.Tensor

inductive IteratorRef : List Nat → Nat → Type where
  | here : IteratorRef (bound :: rest) bound
  | there : IteratorRef rest bound → IteratorRef (other :: rest) bound

abbrev IteratorEnv (bounds : List Nat) := {bound : Nat} → IteratorRef bounds bound → Fin bound

def IteratorEnv.empty : IteratorEnv [] := fun ref => nomatch ref

def IteratorEnv.push (value : Fin bound) (env : IteratorEnv bounds) :
    IteratorEnv (bound :: bounds) := fun ref => match ref with
  | .here => value
  | .there earlier => env earlier

inductive IndexTerm (bounds : List Nat) (extent : Nat) where
  | literal (value : Fin extent)
  | iterator (ref : IteratorRef bounds extent)

def IndexTerm.eval (env : IteratorEnv bounds) : IndexTerm bounds extent → Fin extent
  | .literal value => value
  | .iterator ref => env ref

def IndexTerm.weaken : IndexTerm bounds extent → IndexTerm (bound :: bounds) extent
  | .literal value => .literal value
  | .iterator ref => .iterator (.there ref)

theorem IndexTerm.eval_weaken (term : IndexTerm bounds extent) (value : Fin bound)
    (env : IteratorEnv bounds) : term.weaken.eval (env.push value) = term.eval env := by
  cases term <;> rfl

inductive Subscripts (bounds : List Nat) : List Nat → Type where
  | nil : Subscripts bounds []
  | cons (head : IndexTerm bounds extent) (tail : Subscripts bounds rest) :
      Subscripts bounds (extent :: rest)

def Subscripts.eval (env : IteratorEnv bounds) : Subscripts bounds dims → Coordinates dims
  | .nil => .nil
  | .cons head tail => .cons (head.eval env) (tail.eval env)

def Subscripts.weaken : Subscripts bounds dims → Subscripts (bound :: bounds) dims
  | .nil => .nil
  | .cons head tail => .cons head.weaken tail.weaken

theorem Subscripts.eval_weaken (terms : Subscripts bounds dims) (value : Fin bound)
    (env : IteratorEnv bounds) : terms.weaken.eval (env.push value) = terms.eval env := by
  induction terms with
  | nil => rfl
  | cons head tail ih => simp only [weaken, eval, IndexTerm.eval_weaken, ih]

/-- The interpreter's index conversion matches the independent checked
one-based coordinate decoder, for every loop environment and tensor rank. -/
theorem Subscripts.surface_indices (terms : Subscripts bounds dims) (env : IteratorEnv bounds) :
    Coordinates.fromOneBased dims (terms.eval env).oneBased = some (terms.eval env) :=
  Coordinates.fromOneBased_roundtrip _

/-- A nested iterator with the same extent cannot capture an existing one. -/
theorem IndexTerm.outer_preserved (ref : IteratorRef bounds extent) (value : Fin extent)
    (env : IteratorEnv bounds) :
    (IndexTerm.iterator (.there ref)).eval (env.push value) = env ref := rfl

end Rumoca.GALEC
