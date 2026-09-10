import Std

/-! Value and byte correspondence for eight-bit character objects. Signed
characters use the selected two's-complement profile. The standard library
provides the integer representation and its proved conversions. -/

namespace Rumoca.CCharacter

/-- Value interpretation for an eight-bit character object. Signed characters
use the selected two's-complement C profile; unsigned characters use 0..255. -/
def value (signed : Bool) (byte : UInt8) : Int :=
  if signed then byte.toInt8.toInt else byte.toNat

def inRange (signed : Bool) (n : Int) : Prop :=
  if signed then -128 ≤ n ∧ n < 128 else 0 ≤ n ∧ n < 256

instance (signed : Bool) (n : Int) : Decidable (inRange signed n) := by
  unfold inRange
  infer_instance

/-- Recover the representation of an in-range character value. The inverse
contract requires `inRange`; this is not a general C integer conversion. -/
def byteOf (signed : Bool) (n : Int) : UInt8 :=
  if signed then (Int8.ofInt n).toUInt8 else UInt8.ofNat n.toNat

theorem value_range (signed : Bool) (byte : UInt8) : inRange signed (value signed byte) := by
  cases signed with
  | false =>
    have bound : byte.toNat < 256 := byte.toNat_lt_size
    simp [value, inRange]
    omega
  | true =>
    have lower := byte.toInt8.le_toInt
    have upper := byte.toInt8.toInt_lt
    simp [value, inRange]
    omega

theorem byteOf_value (signed : Bool) (byte : UInt8) : byteOf signed (value signed byte) = byte := by
  cases signed <;> simp [byteOf, value]

theorem value_byteOf (signed : Bool) (n : Int) (bound : inRange signed n) :
    value signed (byteOf signed n) = n := by
  cases signed with
  | false =>
    have hn : 0 ≤ n ∧ n < 256 := by simpa [inRange] using bound
    have hn' : n.toNat < 256 := by omega
    simp [value, byteOf, Nat.mod_eq_of_lt hn']
    omega
  | true =>
    have hn : -128 ≤ n ∧ n < 128 := by simpa [inRange] using bound
    simpa [value, byteOf] using
      (Int8.toInt_ofInt_of_le hn.1 hn.2)

theorem value_injective (signed : Bool) (a b : UInt8) (same : value signed a = value signed b) : a = b := by
  simpa only [byteOf_value] using congrArg (byteOf signed) same

end Rumoca.CCharacter
