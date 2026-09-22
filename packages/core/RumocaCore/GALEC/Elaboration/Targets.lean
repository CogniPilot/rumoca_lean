import RumocaCore.GALEC.Elaboration.Reads

/-! Assignment-target elaboration reuses exactly one resolved reference.
Capability failure never retries lookup. Only the existing output context can
provide writable references; input storage and iterators cannot be assigned. -/
namespace Rumoca.GALEC.Elaboration
open Rumoca.Tensor Rumoca.Solve.Tensor

structure Target (outputs : List Shape) (bounds : List Nat) where
  shape : Shape
  ref : Ref outputs shape
  indices : Subscripts bounds shape.dimensions

def Read.target (read : Read inputs outputs bounds) : Option (Target outputs bounds) :=
  match read.access with
  | .readOnly _ => none
  | .writable ref => some ⟨read.shape, ref, read.indices⟩

inductive Read.IsTarget : Read inputs outputs bounds → Target outputs bounds → Prop where
  | writable {shape : Shape} {ref : Ref outputs shape}
      {indices : Subscripts bounds shape.dimensions} :
      IsTarget ⟨shape, .writable ref, indices⟩ ⟨shape, ref, indices⟩

theorem Read.target_iff (read : Read inputs outputs bounds) (target : Target outputs bounds) :
    read.target = some target ↔ read.IsTarget target := by
  obtain ⟨shape, access, indices⟩ := read
  cases access with
  | readOnly ref =>
    constructor
    · intro impossible; cases impossible
    · intro impossible; cases impossible
  | writable ref =>
    constructor
    · intro found
      cases Option.some.inj found
      exact .writable
    · intro writable
      cases writable
      rfl

namespace TargetLowering

def lower (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (source : AST.Reference) : Option (Target outputs bounds) :=
  (ReadLowering.lower table names source).bind Read.target

inductive Elaborates (table : BindingTable inputs outputs) (names : IteratorNames bounds) :
    AST.Reference → Target outputs bounds → Prop where
  | writable : ReadLowering.Elaborates table names source ⟨shape, .writable ref, indices⟩ →
      Elaborates table names source ⟨shape, ref, indices⟩

theorem lower_iff (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (source : AST.Reference) (target : Target outputs bounds) :
    lower table names source = some target ↔ Elaborates table names source target := by
  simp only [lower, Option.bind_eq_some_iff, Read.target_iff]
  constructor
  · rintro ⟨read, lowered, writable⟩
    cases writable
    exact .writable ((ReadLowering.lower_iff _ _ _ _).mp lowered)
  · intro typed
    cases typed with
    | writable reference =>
      exact ⟨_, (ReadLowering.lower_iff _ _ _ _).mpr reference, .writable⟩

/-- Read-only capability rejection cannot bypass the resolved first binding. -/
theorem readOnly_rejected (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (source : AST.Reference) (ref : Ref inputs shape) (indices : Subscripts bounds shape.dimensions)
    (resolved : ReadLowering.lower table names source = some ⟨shape, .readOnly ref, indices⟩) :
    lower table names source = none := by
  simp only [lower, resolved, Option.bind_some, Read.target]

end TargetLowering
end Rumoca.GALEC.Elaboration
