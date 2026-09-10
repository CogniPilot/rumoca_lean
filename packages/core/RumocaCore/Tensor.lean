import Std

/-! Shared tensor types for Flat, DAE and Solve. Physical storage is a dense
array; rank and extents remain in the type instead of being replaced by volume.
No target ABI or scalar-equation enumeration is part of this representation. -/
namespace Rumoca.Tensor

structure Shape where
  dimensions : List Nat
  deriving Repr, BEq, DecidableEq

def Shape.volume (s : Shape) : Nat := s.dimensions.foldr (· * ·) 1
def scalar : Shape := ⟨[]⟩

/-- A nominal shape parameter prevents exchanging e.g. a 2×3 matrix and a
length-six vector merely because their dense storage has the same length. -/
structure Value (α : Type) (s : Shape) where
  data : Vector α s.volume
  deriving Repr, BEq, DecidableEq

instance : GetElem (Value α s) Nat α (fun _ i => i < s.volume) where
  getElem value i h := value.data[i]

def Value.fill (shape : Shape) (value : α) : Value α shape :=
  ⟨Vector.replicate shape.volume value⟩

@[simp] theorem Value.getElem_fill (shape : Shape) (value : α) (h : i < shape.volume) :
    (Value.fill shape value)[i] = value := by
  change (Vector.replicate shape.volume value)[i] = value
  exact Vector.getElem_replicate h

theorem Value.ext {x y : Value α s} (h : ∀ i (hi : i < s.volume), x[i] = y[i]) : x = y := by
  cases x with
  | mk x =>
    cases y with
    | mk y =>
      have he : x = y := Vector.ext h
      cases he
      rfl

abbrev Denotation (α : Type) (s : Shape) := Fin s.volume → α

end Rumoca.Tensor
