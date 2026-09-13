import RumocaC.StringLiteralContents

/-! A nonzero ASCII source has no hidden terminator in its UTF-8 bytes.
Uses Lean's existing character/list UTF-8 encoding theorems. -/
namespace Rumoca.CStringMemory

def NonzeroASCII (source : String) : Prop :=
  ∀ c ∈ source.toList, 0 < c.toNat ∧ c.toNat < 128

theorem NonzeroASCII.append (left : NonzeroASCII a) (right : NonzeroASCII b) :
    NonzeroASCII (a ++ b) := by
  intro c member
  simp only [String.toList_append, List.mem_append] at member
  exact member.elim (left c) (right c)

private theorem encoded_nonzero (chars : List Char)
    (valid : ∀ c ∈ chars, 0 < c.toNat ∧ c.toNat < 128) :
    ∀ byte ∈ chars.utf8Encode.data.toList, byte ≠ 0 := by
  simp only [List.utf8Encode, List.toList_data_toByteArray]
  intro byte member
  obtain ⟨c, member, encoded⟩ := List.mem_flatMap.mp member
  obtain ⟨positive, bound⟩ := valid c member
  have ascii : c.utf8Size = 1 := by
    rw [Char.utf8Size_eq_one_iff, UInt32.le_iff_toNat_le]
    change c.toNat ≤ 127
    omega
  rw [String.utf8EncodeChar_eq_singleton ascii] at encoded
  obtain rfl := List.mem_singleton.mp encoded
  intro zero
  have zeroNat := congrArg UInt8.toNat zero
  have small : c.val.toNat < 256 := by change c.toNat < 256; omega
  have kept : (c.val.toUInt8).toNat = c.toNat := by
    simp [-Char.toUInt8_val, Nat.mod_eq_of_lt small, Char.toNat]
  rw [kept] at zeroNat
  exact Nat.ne_of_gt positive zeroNat

theorem NonzeroASCII.bytes (valid : NonzeroASCII source) :
    ∀ byte ∈ source.toUTF8.data.toList, byte ≠ 0 := by
  change ∀ byte ∈ source.toByteArray.data.toList, byte ≠ 0
  rw [← String.utf8Encode_toList]
  exact encoded_nonzero source.toList valid

theorem NonzeroASCII.content (valid : NonzeroASCII source) :
    content source = source.toUTF8.data.toList := content_eq valid.bytes

end Rumoca.CStringMemory
