import RumocaCore.GALEC.Elaboration.IteratorIndices

/-! Generic per-axis assembly. The compiler traverses the written index list
and the rank, never the tensor's elements. `lowerIndex` is a compiler function
parameter, not a callback stored in the resulting intrinsic syntax. -/
namespace Rumoca.GALEC.Elaboration.SubscriptLowering
open Rumoca.Tensor

def lower (lowerIndex : (extent : Nat) → AST.Expr → Option (IndexTerm bounds extent)) :
    (dims : List Nat) → List AST.Expr → Option (Subscripts bounds dims)
  | [], [] => some .nil
  | extent :: dims, expr :: expressions =>
      (lowerIndex extent expr).bind fun head =>
        (lower lowerIndex dims expressions).map (Subscripts.cons head)
  | _, _ => none

inductive Elaborates
    (IndexElaborates : (extent : Nat) → AST.Expr → IndexTerm bounds extent → Prop) :
    (dims : List Nat) → List AST.Expr → Subscripts bounds dims → Prop where
  | nil : Elaborates IndexElaborates [] [] .nil
  | cons : IndexElaborates extent expr head → Elaborates IndexElaborates dims expressions tail →
      Elaborates IndexElaborates (extent :: dims) (expr :: expressions) (.cons head tail)

theorem lower_iff
    (lowerIndex : (extent : Nat) → AST.Expr → Option (IndexTerm bounds extent))
    (IndexElaborates : (extent : Nat) → AST.Expr → IndexTerm bounds extent → Prop)
    (correct : ∀ extent expr term, lowerIndex extent expr = some term ↔ IndexElaborates extent expr term)
    (dims : List Nat) (expressions : List AST.Expr) (terms : Subscripts bounds dims) :
    lower lowerIndex dims expressions = some terms ↔ Elaborates IndexElaborates dims expressions terms := by
  induction terms generalizing expressions with
  | nil =>
    cases expressions with
    | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
    | cons expr rest =>
      constructor
      · intro impossible; cases impossible
      · intro impossible; cases impossible
  | @cons extent dims head tail ih =>
    cases expressions with
    | nil =>
      constructor
      · intro impossible; cases impossible
      · intro impossible; cases impossible
    | cons expr rest =>
      simp only [lower, Option.bind_eq_some_iff, Option.map_eq_some_iff]
      constructor
      · rintro ⟨first, firstLowered, remaining, restLowered, same⟩
        cases same
        exact .cons ((correct extent expr head).mp firstLowered) ((ih rest).mp restLowered)
      · intro typed
        cases typed with
        | cons firstTyped restTyped =>
          exact ⟨head, (correct extent expr head).mpr firstTyped,
            tail, (ih rest).mpr restTyped, rfl⟩

theorem rank_preserved
    (typed : Elaborates IndexElaborates dims expressions terms) : expressions.length = dims.length := by
  induction typed with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- Independent per-expression source evaluation, preserving written order. -/
inductive Values (Evaluates : AST.Expr → Int → Prop) : List AST.Expr → List Int → Prop where
  | nil : Values Evaluates [] []
  | cons : Evaluates expr value → Values Evaluates expressions values →
      Values Evaluates (expr :: expressions) (value :: values)

theorem values_correct
    (IndexElaborates : (extent : Nat) → AST.Expr → IndexTerm bounds extent → Prop)
    (Evaluates : AST.Expr → Int → Prop) (env : IteratorEnv bounds)
    (correct : ∀ extent expr term, IndexElaborates extent expr term →
      ∀ value, Evaluates expr value ↔ value = Int.ofNat (term.eval env).val + 1)
    (typed : Elaborates IndexElaborates dims expressions terms) (values : List Int) :
    Values Evaluates expressions values ↔
      values = (terms.eval env).oneBased.map Int.ofNat := by
  induction typed generalizing values with
  | nil =>
    constructor
    · intro h; cases h; rfl
    · rintro rfl; exact .nil
  | @cons extent expr head dims expressions tail first rest ih =>
    constructor
    · intro evaluated
      cases evaluated with
      | cons firstValue restValues =>
        have h := (correct extent expr head first _).mp firstValue
        have t := (ih _).mp restValues
        simp only [Subscripts.eval, Coordinates.oneBased, List.map_cons]
        rw [h, t]
        rfl
    · rintro rfl
      apply Values.cons
      · apply (correct extent expr head first _).mpr
        rfl
      · exact (ih _).mpr rfl

def iterators (names : IteratorNames bounds) (dims : List Nat) (expressions : List AST.Expr) :=
  lower (IteratorIndices.elaborate names) dims expressions

theorem iterators_iff (names : IteratorNames bounds) (dims : List Nat)
    (expressions : List AST.Expr) (terms : Subscripts bounds dims) :
    iterators names dims expressions = some terms ↔
      Elaborates (IteratorIndices.Elaborates names) dims expressions terms :=
  lower_iff _ _ (IteratorIndices.elaborate_iff names) dims expressions terms

theorem iterators_values (names : IteratorNames bounds) (dims : List Nat)
    (expressions : List AST.Expr) (terms : Subscripts bounds dims)
    (lowered : iterators names dims expressions = some terms)
    (env : IteratorEnv bounds) (values : List Int) :
    Values (IteratorIndices.Evaluates names env) expressions values ↔
      values = (terms.eval env).oneBased.map Int.ofNat :=
  values_correct _ _ env (fun _ _ _ typed value => IteratorIndices.lowering_correct typed env value)
    ((iterators_iff names dims expressions terms).mp lowered) values

/-- The actual one-based source values decode to exactly the intrinsic
coordinate, retaining rank and every axis rather than comparing volumes. -/
theorem iterators_decoded (names : IteratorNames bounds) (dims : List Nat)
    (expressions : List AST.Expr) (terms : Subscripts bounds dims)
    (lowered : iterators names dims expressions = some terms)
    (env : IteratorEnv bounds) (values : List Int)
    (evaluated : Values (IteratorIndices.Evaluates names env) expressions values) :
    Coordinates.fromOneBased dims (values.map Int.toNat) = some (terms.eval env) := by
  have actual := (iterators_values names dims expressions terms lowered env values).mp evaluated
  have indices : values.map Int.toNat = (terms.eval env).oneBased := by
    rw [actual]
    simp [Function.comp_def]
  rw [indices]
  exact Coordinates.fromOneBased_roundtrip _

private theorem coordinate_bounds (coordinate : Coordinates dims) :
    List.Forall₂ (fun extent value => (1 : Int) ≤ value ∧ value ≤ Int.ofNat extent)
      dims (coordinate.oneBased.map Int.ofNat) := by
  induction coordinate with
  | nil => exact .nil
  | @cons extent rest index tail ih =>
    apply List.Forall₂.cons _ ih
    have bounded := index.isLt
    change 1 ≤ (index.val : Int) + 1 ∧ (index.val : Int) + 1 ≤ (extent : Int)
    omega

/-- No negative Integer is silently made acceptable by `Int.toNat` in the
decoder theorem: source evaluation already establishes positive axis bounds. -/
theorem iterators_bounds (names : IteratorNames bounds) (dims : List Nat)
    (expressions : List AST.Expr) (terms : Subscripts bounds dims)
    (lowered : iterators names dims expressions = some terms)
    (env : IteratorEnv bounds) (values : List Int)
    (evaluated : Values (IteratorIndices.Evaluates names env) expressions values) :
    List.Forall₂ (fun extent value => (1 : Int) ≤ value ∧ value ≤ Int.ofNat extent) dims values := by
  rw [(iterators_values names dims expressions terms lowered env values).mp evaluated]
  exact coordinate_bounds _

end Rumoca.GALEC.Elaboration.SubscriptLowering
