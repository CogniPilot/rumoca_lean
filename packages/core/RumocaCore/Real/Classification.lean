import RumocaCore.Real.AdditionResult

/-! Numerical classification, independent of interface error/status policy.
All bit patterns are covered, including every NaN payload and both zero signs.
This is not a proof about native classification functions or exception traps. -/
namespace Rumoca.Float64

def Number.isFinite : Number → Bool
  | .finite _ => true
  | _ => false

theorem Number.isFinite_iff (n : Number) :
    n.isFinite = true ↔ ∃ value, n = .finite value := by
  cases n <;> simp [Number.isFinite]

theorem Number.not_finite_iff (n : Number) :
    n.isFinite = false ↔ n = .negativeInfinity ∨ n = .positiveInfinity ∨ n = .nan := by
  cases n <;> simp [Number.isFinite]

/-- The finite encoding interval, not a comparison of floating values. -/
def finiteBits (bits : BitVec 64) : Bool :=
  decide (bits.toNat % Binary64.signPlace < Binary64.magnitudeCount)

theorem finiteBits_decode (bits : BitVec 64) :
    finiteBits bits = (decode bits).isFinite := by
  unfold finiteBits decode
  split
  · simp_all [Number.isFinite]
  · split
    · split <;> simp_all [Number.isFinite]
    · simp_all [Number.isFinite]

@[simp] theorem finiteBits_encode (n : Number) :
    finiteBits n.encode = n.isFinite := by
  rw [finiteBits_decode, decode_encode]

theorem finiteBits_iff (bits : BitVec 64) :
    finiteBits bits = true ↔ ∃ value, bits = (Binary64.toBits value).val := by
  constructor
  · intro h
    have valid : bits.toNat % Binary64.signPlace < Binary64.magnitudeCount :=
      of_decide_eq_true h
    exact ⟨Binary64.ofBits ⟨bits, valid⟩,
      (congrArg Subtype.val (Binary64.toBits_ofBits ⟨bits, valid⟩)).symm⟩
  · rintro ⟨value, rfl⟩
    exact decide_eq_true (Binary64.toBits value).property

end Rumoca.Float64
