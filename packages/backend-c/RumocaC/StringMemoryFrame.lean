import RumocaC.StringMemory

/-! Preserve a caller string using exactly its character cells, including the
terminating zero. The string may be writable; whole-heap equality and a native
string-library result are not preconditions. -/
namespace Rumoca.CStringMemory
open CMemory

/-- Every byte of a stored string, including its terminator, is readable. -/
theorem Contents.readable (stored : Contents heap base bytes) (bound : i ≤ bytes.length) :
    ∃ byte, CLiteral.readByte heap (base.index i) = some byte := by
  induction stored generalizing i with
  | nil terminator =>
    have zero : i = 0 := by simpa using bound
    exact ⟨0, by simpa [zero] using terminator⟩
  | @cons base byte bytes nonzero head tail ih =>
    cases i with
    | zero => exact ⟨byte, by simpa using head⟩
    | succ i =>
      have shift : (base.index 1).index i = base.index (i + 1) := by
        cases base
        simp [Address.index, Nat.add_comm, Nat.add_left_comm]
      simpa only [shift] using ih (Nat.le_of_succ_le_succ bound)

theorem Contents.load_ne_none (stored : Contents heap base bytes) (bound : i ≤ bytes.length) :
    load heap (base.index i) ≠ none := by
  obtain ⟨byte, read⟩ := stored.readable bound
  intro unloaded
  cases cell : heap (base.index i) with
  | none => simp [CLiteral.readByte, cell] at read
  | some object =>
    cases kind : object.type <;> simp [CLiteral.readByte, cell, kind, unloaded] at read

theorem Contents.framed (stored : Contents before base bytes)
    (frame : ∀ i ≤ bytes.length, after (base.index i) = before (base.index i)) :
    Contents after base bytes := by
  induction stored generalizing after with
  | nil terminator =>
    apply Contents.nil
    have same := frame 0 (by simp)
    simp only [Address.index_zero] at same
    simpa only [CLiteral.readByte, load, same] using terminator
  | @cons base byte bytes nonzero head tail ih =>
    refine .cons nonzero ?_ ?_
    · have same := frame 0 (by simp)
      simp only [Address.index_zero] at same
      simpa only [CLiteral.readByte, load, same] using head
    · apply ih
      intro i inside
      have shift : (base.index 1).index i = base.index (i + 1) := by
        cases base
        simp [Address.index, Nat.add_comm, Nat.add_left_comm]
      rw [shift]
      exact frame (i + 1) (by simpa using Nat.add_le_add_right inside 1)

end Rumoca.CStringMemory
