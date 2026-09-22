import RumocaCore.GALEC.Elaboration.Loops.UnitRange
import RumocaCore.GALEC.Elaboration.Loops.Binder

/-! Compile a loop header from its actual AST fields. The result contains the
fresh binder and mathematical count; the body lowerer must still consume the
original statement list in the extended intrinsic context. -/
namespace Rumoca.GALEC.Elaboration.Loops.Header
open Elaboration Rumoca.Tensor _root_.Parser

def read (names : IteratorNames bounds) (lookupShape : List String → Option Shape)
    (ceiling : Nat) (binder : Token) (start : AST.Expr) (stride : Option AST.Expr) (stop : AST.Expr) :
    Option (String × Nat) :=
  (Binder.read names binder).bind fun name =>
    (UnitRange.read lookupShape ceiling start stride stop).map fun count => (name, count)

inductive Denotes (names : IteratorNames bounds) (HasShape : List String → Shape → Prop)
    (ceiling : Nat) : Token → AST.Expr → Option AST.Expr → AST.Expr → String → Nat → Prop where
  | header : Binder.Accepts names binder name → UnitRange.Denotes HasShape ceiling start stride stop count →
      Denotes names HasShape ceiling binder start stride stop name count

theorem read_iff (names : IteratorNames bounds) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) (binder : Token) (start : AST.Expr) (stride : Option AST.Expr) (stop : AST.Expr)
    (name : String) (count : Nat) :
    read names lookupShape ceiling binder start stride stop = some (name, count) ↔
      Denotes names HasShape ceiling binder start stride stop name count := by
  constructor
  · intro found
    obtain ⟨actualName, named, range⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨actualCount, counted, same⟩ := Option.map_eq_some_iff.mp range
    cases same
    exact .header ((Binder.read_iff _ _ _).mp named) ((UnitRange.read_iff _ _ correct _ _ _ _ _).mp counted)
  · intro denoted
    cases denoted with
    | header named counted =>
      simp only [read, (Binder.read_iff _ _ _).mpr named, Option.bind_some,
        (UnitRange.read_iff _ _ correct _ _ _ _ _).mpr counted, Option.map_some]

theorem binder_category (denoted : Denotes names HasShape ceiling binder start stride stop name count) :
    binder = Token.ident name := by
  cases denoted with
  | header accepted _ => cases accepted; rfl

theorem count_bounds (denoted : Denotes names HasShape ceiling binder start stride stop name count) :
    0 < count ∧ count ≤ ceiling := by
  cases denoted with
  | header _ range => exact UnitRange.count_bounds range

theorem outer_preserved (denoted : Denotes names HasShape ceiling binder start stride stop name count)
    (resolved : IteratorNames.Resolves names other ⟨extent, ref⟩) :
    IteratorNames.Resolves (.cons (bound := count) name names) other ⟨extent, .there ref⟩ := by
  cases denoted with
  | header accepted _ => exact Binder.outer_preserved accepted resolved count

theorem range_executes_iff (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (denoted : Denotes names HasShape ceiling binder start stride stop name count)
    (body : Int → State → State → Prop) (before after : State) :
    UnitRange.Executes HasShape ceiling start stride stop body before after ↔
      Iteration.Executes (fun i : Fin count => body (Int.ofNat i.val + 1)) count before after := by
  cases denoted with
  | header _ range => exact UnitRange.executes_iff lookupShape HasShape correct range body before after

end Rumoca.GALEC.Elaboration.Loops.Header
