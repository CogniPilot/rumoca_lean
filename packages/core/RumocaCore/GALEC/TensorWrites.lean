import RumocaCore.GALEC.BoundedIteration
import RumocaCore.Solve.Tensor.Diagonal

/-! Shape-preserving indexed execution using the shared bounded-iteration
mechanism. These are semantic executions, not compiler-time scalarization:
rank and extents remain in every value and result type. No source syntax,
production admission, arithmetic rewrite or renderer is introduced here. -/
namespace Rumoca.GALEC.TensorWrites
open Rumoca.Tensor Iteration

def write (state : Value α shape) (index : Fin shape.volume) (value : α) : Value α shape :=
  ⟨state.data.set index.val value index.isLt⟩

theorem read_write (state : Value α shape) (index atIndex : Fin shape.volume) (value : α) :
    (write state index value)[atIndex] = if index = atIndex then value else state[atIndex] := by
  change (state.data.set index.val value index.isLt)[atIndex.val] = _
  rw [Vector.getElem_set]
  simp only [Fin.ext_iff]
  rfl

/-- Independent indexed-assignment relation: the addressed cell receives the
value and every other cell retains its exact previous contents. -/
def Writes (before : Value α shape) (index : Fin shape.volume) (value : α)
    (after : Value α shape) : Prop :=
  ∀ atIndex : Fin shape.volume,
    after[atIndex] = if index = atIndex then value else before[atIndex]

theorem write_correct (before : Value α shape) (index : Fin shape.volume) (value : α)
    (after : Value α shape) : Writes before index value after ↔ after = write before index value := by
  constructor
  · intro h
    apply Value.ext
    intro i hi
    exact (h ⟨i, hi⟩).trans (read_write before index ⟨i, hi⟩ value).symm
  · rintro rfl
    exact fun i => read_write before index i value

/-- All RHS values come from a fixed input interpretation. Reading the mutable
destination belongs to a different body and needs its own iteration invariant. -/
def overwrite (values : Fin shape.volume → α) (initial : Value α shape) : Value α shape :=
  run (fun i state => write state i (values i)) initial

theorem overwrite_prefix (values : Fin shape.volume → α) (initial : Value α shape)
    (count : Nat) (within : count ≤ shape.volume) (index : Fin shape.volume) :
    (runPrefix (fun i state => write state i (values i)) count within initial)[index] =
      if index.val < count then values index else initial[index] := by
  induction count with
  | zero => simp [runPrefix]
  | succ count ih =>
    rw [runPrefix, read_write, ih]
    by_cases same : count = index.val
    · simp [same]
    · have different : (⟨count, Nat.lt_of_succ_le within⟩ : Fin shape.volume) ≠ index := by
        intro h
        exact same (congrArg Fin.val h)
      rw [if_neg different]
      have bounds : index.val < count ↔ index.val < count + 1 := by omega
      simp only [bounds]

theorem overwrite_get (values : Fin shape.volume → α) (initial : Value α shape)
    (index : Fin shape.volume) : (overwrite values initial)[index] = values index := by
  simpa only [overwrite, run, if_pos index.isLt] using
    overwrite_prefix values initial shape.volume (Nat.le_refl _) index

theorem overwrite_frame (values : Fin shape.volume → α) (initial : Value α shape)
    (count : Nat) (within : count ≤ shape.volume) (index : Fin shape.volume)
    (untouched : count ≤ index.val) :
    (runPrefix (fun i state => write state i (values i)) count within initial)[index] = initial[index] := by
  rw [overwrite_prefix, if_neg (by omega)]

/-- The loop execution implements a shape-preserving tensor map at every
coordinate, independent of the destination's previous contents. -/
theorem overwrite_eq (values : Fin shape.volume → α) (initial : Value α shape) :
    overwrite values initial = ⟨Vector.ofFn values⟩ := by
  apply Value.ext
  intro i hi
  change (overwrite values initial)[i] = (Vector.ofFn values)[i]
  simpa using overwrite_get values initial ⟨i, hi⟩

theorem overwrite_executes (values : Fin shape.volume → α) (initial final : Value α shape) :
    Executes (fun i before after => Writes before i (values i) after) shape.volume initial final ↔
      final = overwrite values initial :=
  run_correct _ _ (fun i before after => write_correct before i (values i) after) initial final

/-- Pointwise realization uses a runtime loop over shaped operands, without
changing operation order or performing a source-level algebraic rewrite. -/
def binary (ops : ScalarOps α) (op : BinaryOp) (left right initial : Value α shape) :
    Value α shape := overwrite (fun i => op.scalar ops left[i] right[i]) initial

theorem binary_correct (ops : ScalarOps α) (op : BinaryOp)
    (left right initial : Value α shape) : binary ops op left right initial = op.eval ops left right := by
  apply Value.ext
  intro i hi
  change (overwrite _ initial)[i] = _
  exact (overwrite_get _ initial ⟨i, hi⟩).trans
    (op.eval_correct ops left right ⟨i, hi⟩).symm

/-- Semantic diagonal iteration over an immutable coefficient interpretation.
This function is not a callback-bearing IR; typed callers retain their input
shapes and scalar expression syntax. -/
def scatterWith (coefficients : Fin size → α)
    (initial : Value α (matrixShape size size)) : Value α (matrixShape size size) :=
  run (fun i state => write state (matrixIndex (i, i)) (coefficients i)) initial

/-- Scatter one shaped coefficient vector along its square matrix diagonal.
This executes a loop; it does not construct a list of scalar instructions. -/
def scatter (coefficients : Value α shape)
    (initial : Value α (matrixShape shape.volume shape.volume)) :
    Value α (matrixShape shape.volume shape.volume) :=
  scatterWith (fun i => coefficients[i]) initial

theorem scatterWith_prefix (coefficients : Fin size → α)
    (initial : Value α (matrixShape size size))
    (count : Nat) (within : count ≤ size) (row column : Fin size) :
    (runPrefix (fun i state => write state (matrixIndex (i, i)) (coefficients i))
      count within initial)[matrixIndex (row, column)] =
      if row = column ∧ row.val < count then coefficients row
      else initial[matrixIndex (row, column)] := by
  induction count with
  | zero => simp [runPrefix]
  | succ count ih =>
    rw [runPrefix, read_write]
    by_cases sameRow : (⟨count, Nat.lt_of_succ_le within⟩ : Fin size) = row
    · subst row
      by_cases sameColumn : (⟨count, Nat.lt_of_succ_le within⟩ : Fin size) = column
      · subst column
        simp
      · have different : matrixIndex (⟨count, Nat.lt_of_succ_le within⟩,
              ⟨count, Nat.lt_of_succ_le within⟩) ≠
            matrixIndex (⟨count, Nat.lt_of_succ_le within⟩, column) := by
          intro h
          exact sameColumn (congrArg Prod.snd (matrixIndex.injective h))
        rw [if_neg different, ih]
        simp [sameColumn]
    · have different : matrixIndex (⟨count, Nat.lt_of_succ_le within⟩,
            ⟨count, Nat.lt_of_succ_le within⟩) ≠ matrixIndex (row, column) := by
        intro h
        exact sameRow (congrArg Prod.fst (matrixIndex.injective h))
      rw [if_neg different, ih]
      have unequal : count ≠ row.val := fun h => sameRow (Fin.ext h)
      have bounds : row.val < count ↔ row.val < count + 1 := by omega
      simp only [bounds]

theorem scatter_prefix (coefficients : Value α shape)
    (initial : Value α (matrixShape shape.volume shape.volume))
    (count : Nat) (within : count ≤ shape.volume) (row column : Fin shape.volume) :
    (runPrefix (fun i state => write state (matrixIndex (i, i)) coefficients[i])
      count within initial)[matrixIndex (row, column)] =
      if row = column ∧ row.val < count then coefficients[row]
      else initial[matrixIndex (row, column)] :=
  scatterWith_prefix (fun i => coefficients[i]) initial count within row column

theorem scatter_get (coefficients : Value α shape)
    (initial : Value α (matrixShape shape.volume shape.volume)) (row column : Fin shape.volume) :
    (scatter coefficients initial)[matrixIndex (row, column)] =
      if row = column then coefficients[row] else initial[matrixIndex (row, column)] := by
  simpa only [scatter, scatterWith, run, row.isLt, and_true] using
    scatter_prefix coefficients initial shape.volume (Nat.le_refl _) row column

theorem scatterWith_get (coefficients : Fin size → α)
    (initial : Value α (matrixShape size size)) (row column : Fin size) :
    (scatterWith coefficients initial)[matrixIndex (row, column)] =
      if row = column then coefficients row else initial[matrixIndex (row, column)] := by
  simpa only [scatterWith, run, row.isLt, and_true] using
    scatterWith_prefix coefficients initial size (Nat.le_refl _) row column

theorem scatterWith_executes (coefficients : Fin size → α)
    (initial final : Value α (matrixShape size size)) :
    Executes (fun i before after => Writes before (matrixIndex (i, i)) (coefficients i) after)
      size initial final ↔ final = scatterWith coefficients initial :=
  run_correct _ _ (fun i before after => write_correct before (matrixIndex (i, i)) (coefficients i) after)
    initial final

theorem scatter_executes (coefficients : Value α shape)
    (initial final : Value α (matrixShape shape.volume shape.volume)) :
    Executes (fun i before after => Writes before (matrixIndex (i, i)) coefficients[i] after)
      shape.volume initial final ↔ final = scatter coefficients initial :=
  run_correct _ _ (fun i before after => write_correct before (matrixIndex (i, i)) coefficients[i] after)
    initial final

/-- The two-phase loop implementation preserves the coefficient shape and the
full matrix shape. Clearing first gives specified zeros at every off-diagonal
cell, irrespective of the old output contents. -/
def diagonal (zero : α) (coefficients : Value α shape)
    (initial : Value α (matrixShape shape.volume shape.volume)) :
    Value α (matrixShape shape.volume shape.volume) :=
  scatter coefficients (overwrite (fun _ => zero) initial)

theorem diagonal_get (zero : α) (coefficients : Value α shape)
    (initial : Value α (matrixShape shape.volume shape.volume)) (row column : Fin shape.volume) :
    (diagonal zero coefficients initial).toMatrix row column =
      if row = column then coefficients[row] else zero := by
  change (diagonal zero coefficients initial)[matrixIndex (row, column)] = _
  rw [diagonal, scatter_get, overwrite_get]

/-- Both phases execute in order under the independent loop/assignment
relations, including empty shapes. No prior destination initialization premise. -/
theorem diagonal_executes (zero : α) (coefficients : Value α shape)
    (initial final : Value α (matrixShape shape.volume shape.volume)) :
    (∃ cleared,
      Executes (fun i before after => Writes before i zero after)
        (matrixShape shape.volume shape.volume).volume initial cleared ∧
      Executes (fun i before after => Writes before (matrixIndex (i, i)) coefficients[i] after)
        shape.volume cleared final) ↔ final = diagonal zero coefficients initial := by
  simp only [overwrite_executes, scatter_executes]
  constructor
  · rintro ⟨cleared, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, rfl, h⟩

/-- Independent prepared-operation correspondence, for arbitrary shaped
programs, arithmetic, environments and previous destination contents. This
materializes already evaluated coefficients; it does not synthesize AD. -/
theorem diagonal_prepared (program : Solve.Tensor.DiagonalProgram Γ shape)
    (ops : ScalarOps α) (zero one : α) (env : Solve.Tensor.Env α Γ)
    (initial : Value α (matrixShape shape.volume shape.volume)) :
    diagonal zero (program.coefficients.eval ops zero one env) initial =
      program.eval ops zero one env := by
  apply (matrixEquiv).injective
  change (diagonal zero _ initial).toMatrix = (program.eval ops zero one env).toMatrix
  rw [Solve.Tensor.DiagonalProgram.eval_correct]
  ext row column
  rw [diagonal_get]
  simp only [Solve.Tensor.DiagonalProgram.denote, Matrix.of_apply]
  split_ifs
  · exact program.coefficients.eval_correct ops zero one env row
  · rfl

end Rumoca.GALEC.TensorWrites
