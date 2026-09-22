import RumocaCore.Solve.Tensor

/-! Immutable state-binding metadata for core elaboration, not backend name
inference. References retain the existing Solve contexts and full shape.

TODO: construct this table from validated AST declarations, qualified paths,
types, directions, method-specific capabilities and the admitted profile.
First-match lookup does not authorize duplicate source declarations. The roles
below are execution-context capabilities, not blanket eFMI output-direction
rules. No source admission or artifact claim follows from this metadata. -/
namespace Rumoca.GALEC.Elaboration
open Rumoca.Tensor Rumoca.Solve.Tensor

/-- The two existing statement environments remain separate. -/
inductive AccessRef (inputs outputs : List Shape) (shape : Shape) where
  | readOnly (ref : Ref inputs shape)
  | writable (ref : Ref outputs shape)

/-- Read a shaped value without changing either environment. -/
def AccessRef.get (access : AccessRef inputs outputs shape)
    (input : Env α inputs) (state : Env α outputs) : Value α shape :=
  match access with
  | .readOnly ref => input ref
  | .writable ref => state ref

/-- Only the writable role can supply an assignment target. -/
def AccessRef.writeRef : AccessRef inputs outputs shape → Option (Ref outputs shape)
  | .readOnly _ => none
  | .writable ref => some ref

theorem AccessRef.writeRef_iff (access : AccessRef inputs outputs shape)
    (ref : Ref outputs shape) :
    access.writeRef = some ref ↔ access = .writable ref := by
  cases access <;> simp [writeRef]

/-- Shape is existential only in metadata; its typed reference retains it. -/
abbrev BindingValue (inputs outputs : List Shape) :=
  Σ shape : Shape, AccessRef inputs outputs shape

/-- Qualified paths are component lists, never joined dotted strings. -/
abbrev BindingTable (inputs outputs : List Shape) :=
  List (List String × BindingValue inputs outputs)

namespace BindingTable

/-- Resolve the first matching complete key, before any later shape or
capability checks. A rejected first binding must not trigger a tail search. -/
def lookup : BindingTable inputs outputs → List String → Option (BindingValue inputs outputs)
  | [], _ => none
  | (head, value) :: tail, key =>
      if key = head then some value else lookup tail key

/-- Independent first-match judgment over immutable binding metadata. -/
inductive Resolves : BindingTable inputs outputs → List String →
    BindingValue inputs outputs → Prop where
  | here : Resolves ((key, value) :: tail) key value
  | there : key ≠ head → Resolves tail key value →
      Resolves ((head, other) :: tail) key value

/-- Universal soundness/completeness, including repeated keys, arbitrary
qualified component lists, all shapes, both roles and empty tables. -/
theorem lookup_iff (table : BindingTable inputs outputs) (key : List String)
    (value : BindingValue inputs outputs) :
    lookup table key = some value ↔ Resolves table key value := by
  induction table with
  | nil =>
    constructor
    · intro impossible; cases impossible
    · intro impossible; cases impossible
  | cons entry tail ih =>
    obtain ⟨head, first⟩ := entry
    by_cases same : key = head
    · subst head
      constructor
      · intro found
        simp only [lookup] at found
        cases found
        exact .here
      · intro resolved
        cases resolved with
        | here => simp [lookup]
        | there different _ => exact False.elim (different rfl)
    · simp only [lookup, if_neg same]
      constructor
      · intro found
        exact .there same (ih.mp found)
      · intro resolved
        cases resolved with
        | here => exact False.elim (same rfl)
        | there _ inner => exact ih.mpr inner

/-- Every tail, including duplicate-key entries, is hidden by the head key. -/
theorem lookup_head (tail : BindingTable inputs outputs) (key : List String)
    (value : BindingValue inputs outputs) :
    lookup ((key, value) :: tail) key = some value := by
  simp [lookup]

end BindingTable
end Rumoca.GALEC.Elaboration
