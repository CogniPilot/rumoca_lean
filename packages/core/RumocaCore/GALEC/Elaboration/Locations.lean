import RumocaCore.GALEC.Elaboration.Reads

/-! Independent source-address semantics. An address retains its shaped Solve
reference, access role and every coordinate axis; equal stored values do not
identify addresses. This is a semantic package, not replacement statement IR.
Source declaration/scope validation, method capabilities and assignment legality
remain separate; writable context membership is not an eFMI direction policy. -/
namespace Rumoca.GALEC.Elaboration
open Rumoca.Tensor Rumoca.Solve.Tensor

structure Location (inputs outputs : List Shape) where
  shape : Shape
  access : AccessRef inputs outputs shape
  coordinate : Coordinates shape.dimensions

def Read.location (read : Read inputs outputs bounds) (env : IteratorEnv bounds) :
    Location inputs outputs :=
  ⟨read.shape, read.access, read.indices.eval env⟩

def Location.get (location : Location inputs outputs)
    (input : Env α inputs) (state : Env α outputs) : α :=
  (location.access.get input state)[Coordinate.index location.coordinate]

namespace Location

/-- Address meaning is specified from actual source syntax, lexical binding,
mathematical index values and checked decoding. No lowered Read, executable
name lookup, target execution, or store value determines the selected address. -/
inductive Evaluates (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (env : IteratorEnv bounds) : AST.Reference → Location inputs outputs → Prop where
  | indexed {source : AST.Reference} {key : List String} {expressions : List AST.Expr}
      {shape : Shape} {access : AccessRef inputs outputs shape} {integers : List Int}
      {coordinate : Coordinates shape.dimensions}
      (spelling : Path.Surface source key expressions)
      (binding : BindingTable.Resolves table key ⟨shape, access⟩)
      (values : SubscriptLowering.Values (IteratorIndices.Evaluates names env) expressions integers)
      (decoded : Coordinates.fromOneBased shape.dimensions (integers.map Int.toNat) = some coordinate) :
      Evaluates table names env source ⟨shape, access, coordinate⟩

variable {inputs outputs : List Shape} {bounds : List Nat}
  {table : BindingTable inputs outputs} {names : IteratorNames bounds}
  {source : AST.Reference} {read : Read inputs outputs bounds}
  {env : IteratorEnv bounds}

theorem lowering_sound (typed : ReadLowering.Elaborates table names source read)
    (env : IteratorEnv bounds) :
    Evaluates table names env source (read.location env) := by
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

/-- Uniqueness of the selected address, not merely of its current value. -/
theorem evaluates_unique (first : Evaluates table names env source a)
    (second : Evaluates table names env source b) : a = b := by
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

/-- Universal address correspondence for every successfully typed read,
iterator environment and candidate location, without inspecting any store. -/
theorem lowering_correct (typed : ReadLowering.Elaborates table names source read)
    (env : IteratorEnv bounds) (location : Location inputs outputs) :
    Evaluates table names env source location ↔ location = read.location env := by
  constructor
  · intro evaluated
    exact evaluates_unique evaluated (lowering_sound typed env)
  · rintro rfl
    exact lowering_sound typed env

end Location

/-- Exact bridge to the existing independent source-read semantics. No
successful-lowering or typing premise is needed in either direction. -/
theorem ReadLowering.evaluates_iff_location (table : BindingTable inputs outputs)
    (names : IteratorNames bounds) (input : Env α inputs) (state : Env α outputs)
    (env : IteratorEnv bounds) (source : AST.Reference) (value : α) :
    ReadLowering.Evaluates table names input state env source value ↔
      ∃ location, Location.Evaluates table names env source location ∧
        value = location.get input state := by
  constructor
  · intro evaluated
    cases evaluated with
    | @indexed key expressions shape access integers coordinate spelling binding values decoded =>
      exact ⟨⟨shape, access, coordinate⟩, .indexed spelling binding values decoded, rfl⟩
  · rintro ⟨location, addressed, rfl⟩
    cases addressed with
    | indexed spelling binding values decoded =>
      exact .indexed spelling binding values decoded

end Rumoca.GALEC.Elaboration
