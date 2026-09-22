import RumocaCore.GALEC.Elaboration.Bindings
import RumocaCore.GALEC.Elaboration.Path

/-! Generic static dimension queries. Shape lookup is a compiler parameter,
not a callback in IR; it never reads runtime tensor values. This branch accepts
unindexed state references and one-based axes, preserving full shape/rank.
Record-component/type-context extensions can supply another proved shape lookup
without changing this mechanism. -/
namespace Rumoca.GALEC.Elaboration.Static.Dimensions
open Rumoca.Tensor Rumoca.Solve.Tensor Elaboration

def read (lookupShape : List String → Option Shape) (source : AST.Reference) (axis : Nat) : Option Nat :=
  (Path.read source).bind fun
    | (key, []) => (lookupShape key).bind fun shape =>
        match axis with
        | 0 => none
        | position + 1 => shape.dimensions[position]?
    | (_, _ :: _) => none

/-- Independent meaning of the selected declared dimension. -/
inductive Denotes (HasShape : List String → Shape → Prop) : AST.Reference → Nat → Nat → Prop where
  | dimension (spelling : Path.Surface source key []) (shapeKnown : HasShape key shape)
      (selected : shape.dimensions[position]? = some extent) :
      Denotes HasShape source (position + 1) extent

theorem read_iff (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (source : AST.Reference) (axis extent : Nat) :
    read lookupShape source axis = some extent ↔ Denotes HasShape source axis extent := by
  constructor
  · intro found
    obtain ⟨⟨key, indices⟩, spelled, selected⟩ := Option.bind_eq_some_iff.mp found
    cases indices with
    | nil =>
      obtain ⟨shape, shapeFound, selected⟩ := Option.bind_eq_some_iff.mp selected
      cases axis with
      | zero => cases selected
      | succ position =>
        exact .dimension ((Path.read_iff source key []).mp spelled)
          ((correct key shape).mp shapeFound) selected
    | cons first rest => cases selected
  · intro denoted
    cases denoted with
    | dimension spelling shapeKnown selected =>
      simp only [read, Path.read_complete spelling, Option.bind_some, (correct _ _).mpr shapeKnown]
      exact selected

/-- Existing shaped binding metadata supplies a checked shape lookup. -/
def bindingShape (table : BindingTable inputs outputs) (key : List String) : Option Shape :=
  (BindingTable.lookup table key).map Sigma.fst

def HasBindingShape (table : BindingTable inputs outputs) (key : List String) (shape : Shape) : Prop :=
  ∃ access : AccessRef inputs outputs shape, BindingTable.Resolves table key ⟨shape, access⟩

theorem bindingShape_iff (table : BindingTable inputs outputs) (key : List String) (shape : Shape) :
    bindingShape table key = some shape ↔ HasBindingShape table key shape := by
  simp only [bindingShape, Option.map_eq_some_iff, HasBindingShape]
  constructor
  · rintro ⟨⟨actual, access⟩, found, same⟩
    cases same
    exact ⟨access, (BindingTable.lookup_iff table key _).mp found⟩
  · rintro ⟨access, bound⟩
    exact ⟨⟨shape, access⟩, (BindingTable.lookup_iff table key _).mpr bound, rfl⟩

theorem binding_read_iff (table : BindingTable inputs outputs) (source : AST.Reference) (axis extent : Nat) :
    read (bindingShape table) source axis = some extent ↔
      Denotes (HasBindingShape table) source axis extent :=
  read_iff _ _ (bindingShape_iff table) source axis extent

theorem axis_positive (denoted : Denotes HasShape source axis extent) : 0 < axis := by
  cases denoted
  omega

theorem zero_axis_rejected (lookupShape : List String → Option Shape) (source : AST.Reference) :
    read lookupShape source 0 = none := by
  unfold read
  cases Path.read source with
  | none => rfl
  | some found =>
    obtain ⟨key, indices⟩ := found
    cases indices with
    | nil =>
      change (lookupShape key).bind (fun _ => none) = none
      cases lookupShape key <;> rfl
    | cons first rest => rfl

end Rumoca.GALEC.Elaboration.Static.Dimensions
