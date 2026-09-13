import RumocaC.Memory

noncomputable section
namespace Rumoca.CMemory.Value

/-- The executable finiteness check accepts exactly the finite binary64 value
domain, using the existing encoding equivalence and preserving both zeros. -/
theorem isFinite_true_iff (value : Value) :
    value.isFinite = some true ↔ ∃ x : Binary64.Value, value = .finite x := by
  constructor
  · intro finite
    cases value with
    | float64 bits =>
        have valid : bits.toNat % Binary64.signPlace < Binary64.magnitudeCount := by
          simpa only [Value.isFinite, Option.some.injEq, decide_eq_true_eq] using finite
        let encoded : Binary64.FiniteBits := ⟨bits, valid⟩
        refine ⟨Binary64.ofBits encoded, ?_⟩
        exact congrArg Value.float64 (congrArg Subtype.val (Binary64.toBits_ofBits encoded)).symm
    | integer n => simp [Value.isFinite] at finite
    | pointer p => simp [Value.isFinite] at finite
    | void => simp [Value.isFinite] at finite
  · rintro ⟨x, rfl⟩
    exact isFinite_finite x

theorem float64_cases (bits : BitVec 64) :
    (∃ x : Binary64.Value, Value.float64 bits = .finite x) ∨
      (Value.float64 bits).isFinite = some false := by
  by_cases valid : bits.toNat % Binary64.signPlace < Binary64.magnitudeCount
  · exact Or.inl ((isFinite_true_iff _).mp (by simp [Value.isFinite, valid]))
  · exact Or.inr (by simp [Value.isFinite, valid])

end Rumoca.CMemory.Value
