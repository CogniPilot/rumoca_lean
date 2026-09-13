import RumocaC.AtomicStorage
import RumocaC.TypedMemory

/-! Static-duration object initialization in the existing symbolic C memory.
Scalar values follow N1570 6.7.9p10; atomic Boolean static initialization follows
7.17.2.1p2. Record selection keeps its nesting and the enclosing array index.
This profile represents arrays of scalar/record elements, not nested array
declarators. There is no element enumeration or runtime allocation. Padding,
byte layout, complete C type constraints and startup/ABI refinement are separate.
-/
namespace Rumoca.CObject
open CMemory

inductive Shape where
  | scalar (type : CType)
  | record (fields : List (String × Shape))
  deriving Repr

/-- Query a scalar leaf relative to one element. Records are not scalar cells;
nonzero indices within scalar fields are rejected rather than aliased. -/
def Shape.leaf (shape : Shape) (members : List (Nat × String)) (offset : Nat) : Option CType :=
  match members with
  | [] => match shape with
    | .scalar type => if offset = 0 then some type else none
    | .record _ => none
  | (index, name) :: rest =>
    if index = 0 then match shape with
      | .scalar _ => none
      | .record fields => do (← fields.lookup name).leaf rest offset
    else none

@[simp] theorem Shape.leaf_scalar (type : CType) : (Shape.scalar type).leaf [] 0 = some type := rfl

theorem Shape.leaf_member (found : fields.lookup name = some field) :
    (Shape.record fields).leaf ((0, name) :: rest) offset = field.leaf rest offset := by
  simp [Shape.leaf, found]

/-- C's semantic zero is a null pointer for pointer objects, not a claim about
all-zero pointer representation bytes. Float64 uses positive zero. -/
def zero : CType → Value
  | .pointer => .pointer none
  | .float64 => .finite Binary64.positiveZero
  | _ => .integer 0

def zeroCell (type : CType) : Cell := ⟨type, true, some (zero type)⟩

theorem zero_converts (type : CType) : convert type (zero type) = some (zero type) := by
  cases type <;> simp [zero, convert, Value.finite, Value.truth, CUnsigned.value]
  case character signed => cases signed <;> decide +kernel

theorem zero_load (found : heap p = some (zeroCell type)) (ordinary : type ≠ .atomicBoolean) :
    load heap p = some (zero type) :=
  load_converted heap p type true (zero type) found ordinary (zero_converts type)

theorem zero_atomic (found : heap p = some (zeroCell .atomicBoolean)) :
    CAtomicBoolean.read heap p = some false := CAtomicBoolean.read_iff.mpr found

/-- Scalar leaf types in an entire fixed-size array. The first index is the
array element; each subsequent member index is relative to its own record. -/
def arrayLeaf (shape : Shape) (capacity : Nat) (members : List (Nat × String)) (offset : Nat) : Option CType :=
  match members with
  | [] => if offset < capacity then shape.leaf [] 0 else none
  | (index, name) :: rest =>
    if index < capacity then shape.leaf ((0, name) :: rest) offset else none

def cellType (shape : Shape) (block capacity : Nat) (p : Address) : Option CType :=
  if p.block = block then arrayLeaf shape capacity p.members p.offset else none

theorem cellType_block (typed : cellType shape block capacity p = some type) : p.block = block := by
  by_contra different
  simp [cellType, different] at typed

/-- Interpretation of a static declaration at program startup, on a fresh
object domain. Freshness is required by the preservation contract below. -/
def initial (heap : Heap) (shape : Shape) (block capacity : Nat) : Heap := fun p =>
  match cellType shape block capacity p with
  | some type => some (zeroCell type)
  | none => heap p

theorem initial_at (typed : cellType shape block capacity p = some type) :
    initial heap shape block capacity p = some (zeroCell type) := by simp [initial, typed]

theorem initial_frame (outside : cellType shape block capacity p = none) :
    initial heap shape block capacity p = heap p := by simp [initial, outside]

theorem initial_other_block (outside : p.block ≠ block) :
    initial heap shape block capacity p = heap p :=
  initial_frame (by simp [cellType, outside])

theorem initial_scalar (heap : Heap) (type : CType) (block capacity : Nat) (i : Fin capacity) :
    initial heap (.scalar type) block capacity ⟨block, [], i.val⟩ = some (zeroCell type) := by
  apply initial_at
  simp [cellType, arrayLeaf, i.isLt]

theorem initial_member (heap : Heap) (shape : Shape) (block capacity : Nat) (i : Fin capacity)
    (typed : shape.leaf ((0, name) :: rest) offset = some type) :
    initial heap shape block capacity ⟨block, (i.val, name) :: rest, offset⟩ = some (zeroCell type) := by
  apply initial_at
  simp [cellType, arrayLeaf, i.isLt, typed]

theorem initial_readonly (fresh : ∀ p type, cellType shape block capacity p = some type → heap p = none) :
    CReadOnly.Preserves heap (initial heap shape block capacity) := by
  intro p entry found readonly
  cases typed : cellType shape block capacity p with
  | none => exact (initial_frame typed).trans found
  | some type => rw [fresh p type typed] at found; contradiction

/-- The generic static scalar-array interpretation agrees with the existing
atomic startup model; subsequent ownership proofs reuse that model. -/
theorem initial_atomic (heap : Heap) (block capacity : Nat) :
    initial heap (.scalar .atomicBoolean) block capacity = CAtomicBoolean.initial heap block capacity := by
  funext p
  rcases p with ⟨b, members, offset⟩
  cases members with
  | nil => by_cases same : b = block <;> by_cases inside : offset < capacity <;>
      simp [initial, cellType, arrayLeaf, Shape.leaf, CAtomicBoolean.initial, zeroCell, zero,
        CAtomicBoolean.cell, CAtomicBoolean.value, same, inside]
  | cons head tail =>
      rcases head with ⟨index, name⟩
      by_cases same : b = block <;> by_cases inside : index < capacity <;>
        simp [initial, cellType, arrayLeaf, Shape.leaf, CAtomicBoolean.initial, same, inside]

end Rumoca.CObject
