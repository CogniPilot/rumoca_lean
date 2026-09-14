import RumocaCore.Real.Comparison

namespace Rumoca.Float64
open Binary64

/-- Decoding a finite value supplies its exact original encoding, including
the sign of zero. No raw bit pattern is silently canonicalized. -/
theorem finite_encoding {bits : BitVec 64} {value : Binary64.Value}
    (decoded : decode bits = .finite value) : bits = (toBits value).val := by
  by_cases finite : bits.toNat % signPlace < magnitudeCount
  · rw [decode, dif_pos finite] at decoded
    have same : ofBits ⟨bits, finite⟩ = value := Number.finite.inj decoded
    exact (congrArg Subtype.val (toBits_ofBits ⟨bits, finite⟩)).symm.trans
      (congrArg (fun v => (toBits v).val) same)
  · simp only [decode, dif_neg finite] at decoded
    split at decoded
    · split at decoded <;> contradiction
    · contradiction


end Rumoca.Float64
