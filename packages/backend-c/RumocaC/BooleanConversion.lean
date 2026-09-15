import RumocaC.Memory

namespace Rumoca.CMemory

/-- Every successful C Boolean conversion records exactly the tested truth
value and produces the canonical integer representation. -/
theorem boolean_conversion (converted : convert .boolean input = some result) :
    ∃ flag : Bool, input.truth = some flag ∧ result = .integer (if flag then 1 else 0) := by
  cases truth : input.truth with
  | none => simp [convert, truth] at converted
  | some flag => exact ⟨flag, rfl, by simpa [convert, truth] using converted.symm⟩

end Rumoca.CMemory
