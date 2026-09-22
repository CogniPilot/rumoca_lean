import RumocaCore.Tensor.Matrix

/-! Rank-preserving coordinates for typed indexed statements.
No grammar, renderer or admission change. -/
namespace Rumoca.Tensor
open Rumoca.Tensor

inductive Coordinates : List Nat → Type where
  | nil : Coordinates []
  | cons (index : Fin extent) (tail : Coordinates rest) : Coordinates (extent :: rest)

def Coordinates.consEquiv : Coordinates (extent :: rest) ≃ Fin extent × Coordinates rest where
  toFun | .cons i tail => (i, tail)
  invFun pair := .cons pair.1 pair.2
  left_inv c := by cases c; rfl
  right_inv pair := by cases pair; rfl

def Coordinates.linear : (dims : List Nat) → Coordinates dims ≃ Fin (dims.foldr (· * ·) 1)
  | [] => {
      toFun := fun _ => ⟨0, Nat.zero_lt_one⟩
      invFun := fun _ => .nil
      left_inv := by intro c; cases c; rfl
      right_inv := by
        intro i
        apply Fin.ext
        change 0 = i.val
        have bound : i.val < 1 := i.isLt
        omega }
  | extent :: rest =>
      consEquiv.trans ((Equiv.prodCongr (Equiv.refl _) (linear rest)).trans finProdFinEquiv)

abbrev Coordinate (shape : Shape) := Coordinates shape.dimensions

def Coordinate.index : Coordinate shape ≃ Fin shape.volume := Coordinates.linear shape.dimensions

theorem Coordinates.linear_cons (i : Fin extent) (tail : Coordinates rest) :
    (linear (extent :: rest) (.cons i tail)).val =
      (linear rest tail).val + (rest.foldr (· * ·) 1) * i.val := rfl

theorem Coordinate.vector (i : Fin extent) :
    (index (shape := ⟨[extent]⟩) (.cons i .nil)).val = i.val := by
  change 0 + 1 * i.val = i.val
  omega

theorem Coordinate.matrix (row : Fin rows) (column : Fin columns) :
    index (shape := matrixShape rows columns) (.cons row (.cons column .nil)) =
      matrixIndex (row, column) := by
  apply Fin.ext
  change 0 + 1 * column.val + (columns * 1) * row.val = column.val + columns * row.val
  simp

def Coordinates.oneBased : Coordinates dims → List Nat
  | .nil => []
  | .cons i tail => (i.val + 1) :: tail.oneBased

theorem Coordinates.oneBased_length (coordinate : Coordinates dims) :
    coordinate.oneBased.length = dims.length := by
  induction coordinate with
  | nil => rfl
  | cons i tail ih => simp [oneBased, ih]

theorem Coordinates.oneBased_bounds (coordinate : Coordinates dims) :
    List.Forall₂ (fun extent index => 1 ≤ index ∧ index ≤ extent) dims coordinate.oneBased := by
  induction coordinate with
  | nil => exact .nil
  | cons i tail ih =>
    exact .cons (by have := i.isLt; omega) ih

/-- Decode one-based surface indices without losing their rank or extents. -/
def Coordinates.fromOneBased : (dims : List Nat) → List Nat → Option (Coordinates dims)
  | [], [] => some .nil
  | [], _ :: _ => none
  | _ :: _, [] => none
  | extent :: rest, value :: tail =>
      if valid : 0 < value ∧ value ≤ extent then
        (fromOneBased rest tail).map (.cons ⟨value - 1, by omega⟩)
      else none

theorem Coordinates.fromOneBased_roundtrip (coordinate : Coordinates dims) :
    fromOneBased dims coordinate.oneBased = some coordinate := by
  induction coordinate with
  | nil => rfl
  | cons i tail ih =>
    simp only [oneBased, fromOneBased]
    rw [dif_pos (by have := i.isLt; omega), ih]
    rfl

theorem Coordinates.fromOneBased_sound (dims indices)
    (coordinate : Coordinates dims) (decoded : fromOneBased dims indices = some coordinate) :
    coordinate.oneBased = indices := by
  induction dims generalizing indices with
  | nil =>
    cases indices with
    | nil => cases coordinate; rfl
    | cons i rest => simp [fromOneBased] at decoded
  | cons extent rest ih =>
    cases indices with
    | nil => simp [fromOneBased] at decoded
    | cons i tail =>
      simp only [fromOneBased] at decoded
      split at decoded
      · rename_i valid
        cases ht : fromOneBased rest tail with
        | none => simp [ht] at decoded
        | some result =>
          simp only [ht, Option.map_some, Option.some.injEq] at decoded
          subst coordinate
          simp only [oneBased, ih _ _ ht]
          congr 1
          omega
      · contradiction

theorem Coordinates.fromOneBased_iff (coordinate : Coordinates dims) (indices : List Nat) :
    fromOneBased dims indices = some coordinate ↔ indices = coordinate.oneBased := by
  constructor
  · intro h; exact (fromOneBased_sound dims indices coordinate h).symm
  · rintro rfl; exact fromOneBased_roundtrip coordinate

end Rumoca.Tensor
