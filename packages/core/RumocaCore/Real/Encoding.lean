import RumocaCore.Real.Binary64

/-! A bijection between the finite mathematical enumeration and actual 64-bit
IEEE encodings. Exponent 2047 is excluded; both signed zeros are retained. -/
namespace Rumoca.Binary64

def signPlace : Nat := 2 ^ 63
abbrev FiniteBits := { b : BitVec 64 // b.toNat % signPlace < magnitudeCount }

def rawCode (x : Value) : Nat :=
  if x.val < magnitudeCount then x.val else x.val - magnitudeCount + signPlace

theorem rawCode_bound (x : Value) : rawCode x < 2 ^ 64 := by
  have hx := x.isLt
  simp only [rawCode, count, magnitudeCount, fractionCount, signPlace] at *
  split <;> omega

theorem rawCode_magnitude (x : Value) : rawCode x % signPlace = magnitudeCode x := by
  have hx := x.isLt
  simp only [rawCode, magnitudeCode, count, magnitudeCount, fractionCount, signPlace] at *
  split <;> omega

def toBits (x : Value) : FiniteBits :=
  ⟨BitVec.ofNat 64 (rawCode x), by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (rawCode_bound x), rawCode_magnitude]
    exact Nat.mod_lt _ (by decide)⟩

theorem toBits_value (x : Value) : (toBits x).val.toNat = rawCode x := by
  simp only [toBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (rawCode_bound x)]

def ofBits (b : FiniteBits) : Value :=
  ⟨if b.val.toNat < signPlace then b.val.toNat
    else b.val.toNat - signPlace + magnitudeCount, by
    have hb := b.val.isLt
    have hf := b.property
    simp only [count, magnitudeCount, fractionCount, signPlace] at *
    split <;> omega⟩

theorem ofBits_toBits (x : Value) : ofBits (toBits x) = x := by
  apply Fin.ext
  simp only [ofBits, toBits_value]
  have hx := x.isLt
  simp only [rawCode, count, magnitudeCount, fractionCount, signPlace] at *
  split <;> split <;> omega

theorem toBits_ofBits (b : FiniteBits) : toBits (ofBits b) = b := by
  apply Subtype.ext
  apply BitVec.eq_of_toNat_eq
  rw [toBits_value]
  have hb := b.val.isLt
  have hf := b.property
  simp only [rawCode, ofBits, count, magnitudeCount, fractionCount, signPlace] at *
  split <;> split <;> omega

/-- Neither finite bit patterns nor signed zero are lost by the proof model. -/
def finiteEncodingEquiv : Value ≃ FiniteBits :=
  ⟨toBits, ofBits, ofBits_toBits, toBits_ofBits⟩

theorem toBits_exponent (x : Value) :
    (toBits x).val.toNat % signPlace / fractionCount = exponent x := by
  rw [toBits_value, rawCode_magnitude]; rfl

theorem toBits_fraction (x : Value) :
    (toBits x).val.toNat % fractionCount = fraction x := by
  rw [toBits_value]
  have h := rawCode_magnitude x
  have hm : signPlace % fractionCount = 0 := by decide +kernel
  rw [fraction, ← h, Nat.mod_mod_of_dvd]
  exact Nat.dvd_of_mod_eq_zero hm

theorem signed_zero_bits :
    (toBits positiveZero).val.toNat = 0 ∧
    (toBits negativeZero).val.toNat = signPlace := by decide +kernel

end Rumoca.Binary64
