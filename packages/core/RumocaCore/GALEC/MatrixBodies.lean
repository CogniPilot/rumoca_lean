import RumocaCore.GALEC.Statements
import RumocaCore.GALEC.StoreIteration
import RumocaCore.GALEC.MatrixClear

/-! Typed rectangular clearing by two ordinary bounded loops. The outer
iterator denotes rows and the inner iterator columns. No flattening of the
surface matrix reference or enumeration of scalar instructions is used. -/
namespace Rumoca.GALEC.MatrixBodies
open Rumoca.Tensor Rumoca.Solve.Tensor

def matrixSubscripts : Subscripts (cols :: rows :: bounds) [rows, cols] :=
  .cons (.iterator (.there .here)) (.cons (.iterator .here) .nil)

def clearRow (target : Ref outputs (matrixShape rows cols)) : Statement inputs outputs (rows :: bounds) :=
  .bounded cols (.assign target matrixSubscripts (.literal .zero))

def clearMatrix (target : Ref outputs (matrixShape rows cols)) : Statement inputs outputs bounds :=
  .bounded rows (clearRow target)

theorem clear_cell_executes (target : Ref outputs (matrixShape rows cols))
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs)
    (iterators : IteratorEnv bounds) (row : Fin rows) (col : Fin cols) (before after : Env α outputs) :
    (Statement.assign target matrixSubscripts (.literal .zero)).Executes step zero one input
      (IteratorEnv.push col (IteratorEnv.push row iterators)) before after ↔
    ∃ tensor, TensorWrites.Writes (before target) (matrixIndex (row, col)) zero tensor ∧
      Env.Updates before target tensor after := by
  simp only [Statement.Executes, matrixSubscripts, Subscripts.eval, IndexTerm.eval,
    IteratorEnv.push, Coordinate.matrix]
  constructor
  · rintro ⟨result, tensor, evaluated, written, frame⟩
    cases evaluated
    exact ⟨tensor, written, frame⟩
  · rintro ⟨tensor, written, frame⟩
    exact ⟨zero, tensor, .literal .zero, written, frame⟩

theorem clear_row_executes (target : Ref outputs (matrixShape rows cols))
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs)
    (iterators : IteratorEnv bounds) (row : Fin rows) (before after : Env α outputs) :
    (clearRow target).Executes step zero one input (iterators.push row) before after ↔
    Env.Updates before target (MatrixClear.clearRow zero row (before target)) after := by
  change Iteration.Executes (σ := Env α outputs) (fun col current next =>
    (Statement.assign target matrixSubscripts (.literal .zero)).Executes step zero one input
      (IteratorEnv.push col (IteratorEnv.push row iterators)) current next) cols @before @after ↔ _
  simp_rw [clear_cell_executes]
  rw [StoreIteration.executes_iff target
    (fun col first last => TensorWrites.Writes first (matrixIndex (row, col)) zero last) cols before after]
  simp only [MatrixClear.clearRow_executes, exists_eq_left]

/-- Literal clearing needs no arithmetic-totality premise: the arbitrary
scalar relation is never invoked. The complete store frame is retained. -/
theorem clear_matrix_executes (target : Ref outputs (matrixShape rows cols))
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs)
    (iterators : IteratorEnv bounds) (before after : Env α outputs) :
    (clearMatrix target).Executes step zero one input iterators before after ↔
    Env.Updates before target (Value.fill (matrixShape rows cols) zero) after := by
  change Iteration.Executes (σ := Env α outputs) (fun row current next =>
    (clearRow target).Executes step zero one input (iterators.push row) current next)
      rows @before @after ↔ _
  simp_rw [clear_row_executes]
  have lift := StoreIteration.executes_iff target
    (fun row first last => last = MatrixClear.clearRow zero row first) rows before after
  simp only [exists_eq_left] at lift
  rw [lift]
  have runCorrect := Iteration.run_correct (fun row tensor => MatrixClear.clearRow zero row tensor)
    (fun row first last => last = MatrixClear.clearRow zero row first)
    (fun _ _ _ => Iff.rfl) (before target)
  simp only [runCorrect, exists_eq_left]
  change Env.Updates before target (MatrixClear.clearMatrix zero (before target)) after ↔ _
  rw [MatrixClear.clearMatrix_eq_fill]

end Rumoca.GALEC.MatrixBodies
