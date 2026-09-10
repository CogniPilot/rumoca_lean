import RumocaCore.Real.Encoding

/-! Typed cells at symbolic C subobject addresses. Addresses distinguish live
blocks, struct member paths and array offsets. This is an object-level C
memory profile, not a byte-layout/ABI theorem. The current fragment has no
unions, pointer-to-integer casts, allocation, free, or pointer arithmetic
across subobjects. Absent and uninitialized cells cannot be read; writes need
a writable, existing cell and a supported conversion to its declared type.
All Float64 payloads, including non-finite encodings, are stored as 64 bits. -/
namespace Rumoca.CMemory

structure Address where
  block : Nat
  members : List String := []
  offset : Nat := 0
  deriving DecidableEq, Repr

def Address.member (p : Address) (name : String) : Address :=
  { p with members := p.members ++ [name] }
def Address.index (p : Address) (n : Nat) : Address := { p with offset := p.offset + n }

@[simp] theorem Address.index_zero (p : Address) : p.index 0 = p := by cases p; rfl

@[simp] theorem Address.member_inj (p : Address) (a b : String) :
    p.member a = p.member b ↔ a = b := by
  constructor
  · intro h
    have hm := List.append_cancel_left (congrArg Address.members h)
    exact List.singleton_inj.mp hm
  · intro h; cases h; rfl

inductive Value where
  | integer (value : Int)
  | float64 (bits : BitVec 64)
  | pointer (address : Option Address)
  | string (text : String)
  | void
  deriving DecidableEq, Repr

def Value.finite (x : Binary64.Value) : Value := .float64 (Binary64.toBits x).val

def Value.truth : Value → Option Bool
  | .integer n => some (n != 0)
  | .pointer p => some p.isSome
  | .float64 bits => some (bits.toNat % Binary64.signPlace != 0)
  | _ => none

def Value.address : Value → Option Address
  | .pointer (some p) => some p
  | _ => none

def Value.isFinite : Value → Option Bool
  | .float64 bits => some (decide (bits.toNat % Binary64.signPlace < Binary64.magnitudeCount))
  | _ => none

@[simp] theorem Value.isFinite_finite (x : Binary64.Value) :
    (Value.finite x).isFinite = some true := by
  simp only [Value.finite, Value.isFinite, decide_eq_true (Binary64.toBits x).property]

inductive CType where | float64 | int32 | size | boolean | pointer
  deriving DecidableEq, Repr

/-- Partial C conversions for the implemented fragment. Unsupported arithmetic
and casts fail; they never silently become identities or real arithmetic. -/
def convert : CType → Value → Option Value
  | .float64, .float64 b => some (.float64 b)
  | .float64, .integer n =>
    if n = 0 then some (.finite Binary64.positiveZero)
    else if n = 1 then some (.finite Binary64.one) else none
  | .int32, .integer n => if -(2^31 : Int) ≤ n ∧ n < 2^31 then some (.integer n) else none
  | .size, .integer n => if 0 ≤ n ∧ n < 2^64 then some (.integer n) else none
  | .boolean, v => do return .integer (if ← v.truth then 1 else 0)
  | .pointer, .pointer p => some (.pointer p)
  | _, _ => none

structure Cell where
  type : CType
  writable : Bool
  value : Option Value
  deriving DecidableEq, Repr

abbrev Heap := Address → Option Cell

def load (h : Heap) (p : Address) : Option Value := do
  let c ← h p
  let value ← c.value
  let checked ← convert c.type value
  if checked = value then some value else none

def replace (h : Heap) (p : Address) (c : Cell) : Heap := fun q => if q = p then some c else h q

def store (h : Heap) (p : Address) (v : Value) : Option Heap := do
  let c ← h p
  if !c.writable then none else do
    let converted ← convert c.type v
    return replace h p { c with value := some converted }

@[simp] theorem replace_at (h : Heap) (p : Address) (c : Cell) :
    replace h p c p = some c := by simp [replace]

theorem replace_other (h : Heap) (p q : Address) (c : Cell) (hne : q ≠ p) :
    replace h p c q = h q := by simp [replace, hne]

theorem store_float64 (h : Heap) (p : Address) (old : Option Value) (bits : BitVec 64)
    (hp : h p = some ⟨.float64, true, old⟩) :
    store h p (.float64 bits) = some (replace h p ⟨.float64, true, some (.float64 bits)⟩) := by
  simp [store, hp, convert]

theorem store_frame (h : Heap) (p : Address) (v : Value) (h' : Heap)
    (hs : store h p v = some h') (q : Address) (hne : q ≠ p) : h' q = h q := by
  unfold store at hs
  cases hc : h p with
  | none => simp [hc] at hs
  | some c =>
    simp only [hc, bind, Option.bind] at hs
    split at hs
    · contradiction
    · cases hv : convert c.type v with
      | none => simp [hv] at hs
      | some value =>
        simp only [hv, pure, Option.some.injEq] at hs
        subst h'
        exact replace_other _ _ _ _ hne

theorem store_other_block (h : Heap) (p : Address) (v : Value) (h' : Heap)
    (hs : store h p v = some h') (q : Address) (hne : q.block ≠ p.block) : h' q = h q :=
  store_frame h p v h' hs q (fun he => hne (congrArg Address.block he))

theorem store_unallocated (h : Heap) (p : Address) (v : Value) (hp : h p = none) :
    store h p v = none := by simp [store, hp]

theorem store_readonly (h : Heap) (p : Address) (v : Value) (c : Cell)
    (hp : h p = some c) (hw : c.writable = false) : store h p v = none := by
  simp [store, hp, hw]

end Rumoca.CMemory
