import RumocaCore.GALEC.Elaboration.Bindings
import RumocaCore.GALEC.Elaboration.Path
import RumocaCore.GALEC.Elaboration.Subscripts
import RumocaCore.GALEC.Statements

/-! Checked state-read lowering. Names/shapes/capabilities are supplied by core
declaration preparation, never inferred by a backend. The source relation uses
actual AST paths, independent lookup/index evaluation and one-based decoding.
No whole declaration or artifact acceptance claim is made by this module. -/
namespace Rumoca.GALEC.Elaboration
open Rumoca.Tensor Rumoca.Solve.Tensor

structure Read (inputs outputs : List Shape) (bounds : List Nat) where
  shape : Shape
  access : AccessRef inputs outputs shape
  indices : Subscripts bounds shape.dimensions

def Read.term (read : Read inputs outputs bounds) : ScalarTerm inputs outputs bounds :=
  match read.access with
  | .readOnly ref => .input ref read.indices
  | .writable ref => .output ref read.indices

def Read.value (read : Read inputs outputs bounds) (input : Env α inputs)
    (state : Env α outputs) (env : IteratorEnv bounds) : α :=
  (read.access.get input state)[Coordinate.index (read.indices.eval env)]

theorem Read.term_evaluates (read : Read inputs outputs bounds)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) (state : Env α outputs) (env : IteratorEnv bounds) (value : α) :
    read.term.Evaluates step zero one input state env value ↔ value = read.value input state env := by
  obtain ⟨shape, access, indices⟩ := read
  cases access with
  | readOnly ref =>
    constructor
    · intro h; cases h; rfl
    · rintro rfl; exact .input ref indices
  | writable ref =>
    constructor
    · intro h; cases h; rfl
    · rintro rfl; exact .output ref indices

namespace ReadLowering

def lower (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (source : AST.Reference) : Option (Read inputs outputs bounds) :=
  (Path.read source).bind fun (key, expressions) =>
    (BindingTable.lookup table key).bind fun ⟨shape, access⟩ =>
      (SubscriptLowering.iterators names shape.dimensions expressions).map
        fun indices => ⟨shape, access, indices⟩

inductive Elaborates (table : BindingTable inputs outputs) (names : IteratorNames bounds) :
    AST.Reference → Read inputs outputs bounds → Prop where
  | indexed (spelling : Path.Surface source key expressions)
      (binding : BindingTable.Resolves table key ⟨shape, access⟩)
      (typed : SubscriptLowering.Elaborates (IteratorIndices.Elaborates names)
        shape.dimensions expressions indices) :
      Elaborates table names source ⟨shape, access, indices⟩

theorem lower_iff (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (source : AST.Reference) (read : Read inputs outputs bounds) :
    lower table names source = some read ↔ Elaborates table names source read := by
  simp only [lower, Option.bind_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨key, expressions⟩, spelled, ⟨shape, access⟩, bound, indices, typed, same⟩
    cases same
    exact .indexed ((Path.read_iff source key expressions).mp spelled)
      ((BindingTable.lookup_iff table key ⟨shape, access⟩).mp bound)
      ((SubscriptLowering.iterators_iff names shape.dimensions expressions indices).mp typed)
  · intro typed
    cases typed with
    | @indexed key expressions shape access indices spelling binding typedIndices =>
      exact ⟨⟨key, expressions⟩, Path.read_complete spelling, ⟨shape, access⟩,
        (BindingTable.lookup_iff table key ⟨shape, access⟩).mpr binding, indices,
        (SubscriptLowering.iterators_iff names shape.dimensions expressions indices).mpr typedIndices, rfl⟩

/-- Source read semantics contains no lowered Read/ScalarTerm or executable
lookup. The independent index values must decode at this declaration's shape. -/
inductive Evaluates (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (input : Env α inputs) (state : Env α outputs) (env : IteratorEnv bounds) :
    AST.Reference → α → Prop where
  | indexed (spelling : Path.Surface source key expressions)
      (binding : BindingTable.Resolves table key ⟨shape, access⟩)
      (values : SubscriptLowering.Values (IteratorIndices.Evaluates names env) expressions integers)
      (decoded : Coordinates.fromOneBased shape.dimensions (integers.map Int.toNat) = some coordinate) :
      Evaluates table names input state env source
        ((access.get input state)[Coordinate.index coordinate])

variable {inputs outputs : List Shape} {bounds : List Nat}
  {table : BindingTable inputs outputs} {names : IteratorNames bounds}
  {source : AST.Reference} {read : Read inputs outputs bounds}
  {input : Env α inputs} {state : Env α outputs} {env : IteratorEnv bounds}

theorem lowering_sound (typed : Elaborates table names source read)
    (input : Env α inputs) (state : Env α outputs) (env : IteratorEnv bounds) :
    Evaluates table names input state env source (read.value input state env) := by
  cases typed with
  | @indexed key expressions shape access indices spelling binding typedIndices =>
    have lowered := (SubscriptLowering.iterators_iff names shape.dimensions expressions indices).mpr typedIndices
    have evaluated := (SubscriptLowering.iterators_values names shape.dimensions expressions indices
      lowered env ((indices.eval env).oneBased.map Int.ofNat)).mpr rfl
    exact .indexed spelling binding evaluated
      (SubscriptLowering.iterators_decoded names shape.dimensions expressions indices lowered env _ evaluated)

private theorem index_values_unique
    (first : SubscriptLowering.Values (IteratorIndices.Evaluates names env) expressions a)
    (second : SubscriptLowering.Values (IteratorIndices.Evaluates names env) expressions b) : a = b := by
  induction first generalizing b with
  | nil => cases second; rfl
  | cons head rest ih =>
    cases second with
    | cons otherHead otherRest =>
      exact congrArg₂ List.cons (IteratorIndices.evaluates_unique head otherHead) (ih otherRest)

theorem evaluates_unique (first : Evaluates table names input state env source a)
    (second : Evaluates table names input state env source b) : a = b := by
  cases first with
  | @indexed key expressions shape access integers coordinate spelling binding values decoded =>
    cases second with
    | @indexed otherKey otherExpressions otherShape otherAccess otherIntegers otherCoordinate
        otherSpelling otherBinding otherValues otherDecoded =>
      have samePath := Option.some.inj
        ((Path.read_complete spelling).symm.trans (Path.read_complete otherSpelling))
      cases samePath
      have sameBinding := Option.some.inj
        (((BindingTable.lookup_iff table key ⟨shape, access⟩).mpr binding).symm.trans
          ((BindingTable.lookup_iff table key ⟨otherShape, otherAccess⟩).mpr otherBinding))
      cases sameBinding
      have sameValues := index_values_unique values otherValues
      subst otherIntegers
      have sameCoordinate := Option.some.inj (decoded.symm.trans otherDecoded)
      cases sameCoordinate
      rfl

theorem lowering_correct (typed : Elaborates table names source read)
    (input : Env α inputs) (state : Env α outputs) (env : IteratorEnv bounds) (value : α) :
    Evaluates table names input state env source value ↔ value = read.value input state env := by
  constructor
  · intro evaluated
    exact evaluates_unique evaluated (lowering_sound typed input state env)
  · rintro rfl
    exact lowering_sound typed input state env

/-- Actual source-reference success composes to the existing target expression
execution relation, for arbitrary partial arithmetic and every store. -/
theorem source_to_term (lowered : lower table names source = some read)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) (state : Env α outputs) (env : IteratorEnv bounds) (value : α) :
    Evaluates table names input state env source value ↔
      read.term.Evaluates step zero one input state env value :=
  (lowering_correct ((lower_iff table names source read).mp lowered) input state env value).trans
    (read.term_evaluates step zero one input state env value).symm

end ReadLowering
end Rumoca.GALEC.Elaboration
