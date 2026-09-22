import RumocaCore.GALEC.TensorWrites

/-! Rectangular rank-two clearing by nested runtime iteration. No flattened
instruction list, shape erasure, arithmetic, typed Statement or Env API. -/
namespace Rumoca.GALEC.MatrixClear
open Rumoca.Tensor Rumoca.GALEC.Iteration Rumoca.GALEC.TensorWrites

variable {α : Type} {rows cols : Nat}

def clearRow (zero : α) (row : Fin rows)
    (initial : Value α (matrixShape rows cols)) : Value α (matrixShape rows cols) :=
  run (fun col state => write state (matrixIndex (row, col)) zero) initial

def clearMatrix (zero : α) (initial : Value α (matrixShape rows cols)) :
    Value α (matrixShape rows cols) :=
  run (fun row state => clearRow zero row state) initial

/-- Exact row prefix: only the chosen row and columns strictly before count
are changed. All other old values are retained, with no assumptions on them. -/
theorem clearRow_prefix_get (zero : α) (row : Fin rows)
    (initial : Value α (matrixShape rows cols)) (count : Nat) (within : count ≤ cols)
    (atRow : Fin rows) (atCol : Fin cols) :
    (runPrefix (fun col state => write state (matrixIndex (row, col)) zero)
      count within initial)[matrixIndex (atRow, atCol)] =
      if row = atRow ∧ atCol.val < count then zero else initial[matrixIndex (atRow, atCol)] := by
  induction count with
  | zero => simp [runPrefix]
  | succ count ih =>
    rw [runPrefix, read_write]
    by_cases sameRow : row = atRow
    · subst atRow
      by_cases sameCol : (⟨count, Nat.lt_of_succ_le within⟩ : Fin cols) = atCol
      · subst atCol
        simp
      · have different : matrixIndex (row, (⟨count, Nat.lt_of_succ_le within⟩ : Fin cols)) ≠
            matrixIndex (row, atCol) := by
          intro h
          exact sameCol (congrArg Prod.snd (matrixIndex.injective h))
        rw [if_neg different, ih]
        have unequal : count ≠ atCol.val := fun h => sameCol (Fin.ext h)
        have bounds : atCol.val < count ↔ atCol.val < count + 1 := by omega
        simp only [bounds]
    · have different : matrixIndex (row, (⟨count, Nat.lt_of_succ_le within⟩ : Fin cols)) ≠
          matrixIndex (atRow, atCol) := by
        intro h
        exact sameRow (congrArg Prod.fst (matrixIndex.injective h))
      rw [if_neg different, ih]
      simp only [sameRow, false_and, if_false]

theorem clearRow_prefix_frame (zero : α) (row : Fin rows)
    (initial : Value α (matrixShape rows cols)) (count : Nat) (within : count ≤ cols)
    (atRow : Fin rows) (atCol : Fin cols)
    (untouched : row ≠ atRow ∨ count ≤ atCol.val) :
    (runPrefix (fun col state => write state (matrixIndex (row, col)) zero)
      count within initial)[matrixIndex (atRow, atCol)] = initial[matrixIndex (atRow, atCol)] := by
  rw [clearRow_prefix_get, if_neg]
  rcases untouched with h | h
  · exact fun both => h both.1
  · exact fun both => Nat.not_lt_of_ge h both.2

theorem clearRow_get (zero : α) (row : Fin rows)
    (initial : Value α (matrixShape rows cols)) (atRow : Fin rows) (atCol : Fin cols) :
    (clearRow zero row initial)[matrixIndex (atRow, atCol)] =
      if row = atRow then zero else initial[matrixIndex (atRow, atCol)] := by
  simpa only [clearRow, run, atCol.isLt, and_true] using
    clearRow_prefix_get zero row initial cols (Nat.le_refl _) atRow atCol

theorem clearRow_at (zero : α) (row : Fin rows)
    (initial : Value α (matrixShape rows cols)) (col : Fin cols) :
    (clearRow zero row initial)[matrixIndex (row, col)] = zero := by
  rw [clearRow_get, if_pos rfl]

theorem clearRow_frame (zero : α) (row : Fin rows)
    (initial : Value α (matrixShape rows cols)) (atRow : Fin rows) (atCol : Fin cols)
    (untouched : row ≠ atRow) :
    (clearRow zero row initial)[matrixIndex (atRow, atCol)] = initial[matrixIndex (atRow, atCol)] := by
  rw [clearRow_get, if_neg untouched]

/-- After count complete rows, precisely the cells in earlier rows are cleared. -/
theorem clearMatrix_prefix_get (zero : α) (initial : Value α (matrixShape rows cols))
    (count : Nat) (within : count ≤ rows) (row : Fin rows) (col : Fin cols) :
    (runPrefix (fun r state => clearRow zero r state) count within initial)[matrixIndex (row, col)] =
      if row.val < count then zero else initial[matrixIndex (row, col)] := by
  induction count with
  | zero => simp [runPrefix]
  | succ count ih =>
    rw [runPrefix, clearRow_get]
    by_cases sameRow : (⟨count, Nat.lt_of_succ_le within⟩ : Fin rows) = row
    · subst row
      simp
    · rw [if_neg sameRow, ih]
      have unequal : count ≠ row.val := fun h => sameRow (Fin.ext h)
      have bounds : row.val < count ↔ row.val < count + 1 := by omega
      simp only [bounds]

theorem clearMatrix_prefix_frame (zero : α) (initial : Value α (matrixShape rows cols))
    (count : Nat) (within : count ≤ rows) (row : Fin rows) (col : Fin cols)
    (untouched : count ≤ row.val) :
    (runPrefix (fun r state => clearRow zero r state) count within initial)[matrixIndex (row, col)] =
      initial[matrixIndex (row, col)] := by
  rw [clearMatrix_prefix_get, if_neg (Nat.not_lt_of_ge untouched)]

/-- Exact intermediate state inside the next row, following all earlier rows. -/
theorem clearMatrix_row_prefix_get (zero : α) (initial : Value α (matrixShape rows cols))
    (activeRow : Fin rows) (count : Nat) (within : count ≤ cols)
    (row : Fin rows) (col : Fin cols) :
    (runPrefix (fun c state => write state (matrixIndex (activeRow, c)) zero) count within
      (runPrefix (fun r state => clearRow zero r state) activeRow.val
        (Nat.le_of_lt activeRow.isLt) initial))[matrixIndex (row, col)] =
      if row.val < activeRow.val ∨ activeRow = row ∧ col.val < count
      then zero else initial[matrixIndex (row, col)] := by
  rw [clearRow_prefix_get, clearMatrix_prefix_get]
  by_cases earlier : row.val < activeRow.val <;>
    by_cases current : activeRow = row ∧ col.val < count <;> simp [earlier, current]

theorem clearMatrix_row_prefix_frame (zero : α) (initial : Value α (matrixShape rows cols))
    (activeRow : Fin rows) (count : Nat) (within : count ≤ cols)
    (row : Fin rows) (col : Fin cols)
    (notEarlier : activeRow.val ≤ row.val)
    (untouched : activeRow ≠ row ∨ count ≤ col.val) :
    (runPrefix (fun c state => write state (matrixIndex (activeRow, c)) zero) count within
      (runPrefix (fun r state => clearRow zero r state) activeRow.val
        (Nat.le_of_lt activeRow.isLt) initial))[matrixIndex (row, col)] =
      initial[matrixIndex (row, col)] := by
  rw [clearMatrix_row_prefix_get, if_neg]
  intro changed
  rcases changed with earlier | current
  · exact Nat.not_lt_of_ge notEarlier earlier
  · rcases untouched with otherRow | laterCol
    · exact otherRow current.1
    · exact Nat.not_lt_of_ge laterCol current.2

theorem clearMatrix_get (zero : α) (initial : Value α (matrixShape rows cols))
    (row : Fin rows) (col : Fin cols) :
    (clearMatrix zero initial)[matrixIndex (row, col)] = zero := by
  simpa only [clearMatrix, run, if_pos row.isLt] using
    clearMatrix_prefix_get zero initial rows (Nat.le_refl _) row col

/-- Rectangular, arbitrary old contents, arbitrary replacement value; zero
rows/columns require no exceptional branch or positive-extent assumption. -/
theorem clearMatrix_eq_fill (zero : α) (initial : Value α (matrixShape rows cols)) :
    clearMatrix zero initial = Value.fill (matrixShape rows cols) zero := by
  apply matrixEquiv.injective
  change (clearMatrix zero initial).toMatrix = (Value.fill (matrixShape rows cols) zero).toMatrix
  ext row col
  change (clearMatrix zero initial)[matrixIndex (row, col)] =
    (Value.fill (matrixShape rows cols) zero)[matrixIndex (row, col)]
  rw [clearMatrix_get]
  exact (Value.getElem_fill _ _ (matrixIndex (row, col)).isLt).symm

theorem clearMatrix_zero_rows (zero : α) (initial : Value α (matrixShape 0 cols)) :
    clearMatrix zero initial = initial := rfl

theorem clearMatrix_zero_cols (zero : α) (initial : Value α (matrixShape rows 0)) :
    clearMatrix zero initial = initial := by
  apply matrixEquiv.injective
  change (clearMatrix zero initial).toMatrix = initial.toMatrix
  ext row col
  exact Fin.elim0 col

theorem clearRow_executes (zero : α) (row : Fin rows)
    (initial final : Value α (matrixShape rows cols)) :
    Executes (fun col before after => Writes before (matrixIndex (row, col)) zero after)
      cols initial final ↔ final = clearRow zero row initial :=
  run_correct _ _ (fun col before after => write_correct before (matrixIndex (row, col)) zero after)
    initial final

theorem clearMatrix_executes (zero : α) (initial final : Value α (matrixShape rows cols)) :
    Executes (fun row before after =>
      Executes (fun col first last => Writes first (matrixIndex (row, col)) zero last)
        cols before after) rows initial final ↔ final = Value.fill (matrixShape rows cols) zero := by
  rw [← clearMatrix_eq_fill zero initial]
  exact run_correct _ _ (fun row before after => clearRow_executes zero row before after) initial final

end Rumoca.GALEC.MatrixClear
