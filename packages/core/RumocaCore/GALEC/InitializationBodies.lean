import RumocaCore.GALEC.VectorClear
import RumocaCore.GALEC.MatrixBodies

/-! A shaped core initialization sequence and an independent final-store
specification. This does not select source declarations or method permissions. -/
namespace Rumoca.GALEC.InitializationBodies
open Rumoca.Tensor Rumoca.Solve.Tensor

/-- Existing statement constructors only; the three extents are independent. -/
def body (vector : Ref outputs ⟨[extent]⟩) (matrix : Ref outputs (matrixShape rows cols))
    (period : Ref outputs scalar) : Statement inputs outputs bounds :=
  .seq (VectorClear.clearVector vector)
    (.seq (MatrixBodies.clearMatrix matrix) (.assign period .nil (.literal .one)))

/-- A rank-zero write replaces the entire scalar-shaped value. -/
theorem scalar_write_iff (before after : Value α scalar) (value : α) :
    TensorWrites.Writes before (Coordinate.index .nil) value after ↔
      after = Value.fill scalar value := by
  constructor
  · intro written
    apply Value.ext
    intro i hi
    have same : (Coordinate.index .nil : Fin scalar.volume) = ⟨i, hi⟩ :=
      Subsingleton.elim (α := Fin 1) _ _
    have selected : after[i] = value := by
      simpa only [if_pos same] using written ⟨i, hi⟩
    exact selected.trans
      (Value.getElem_fill scalar value hi).symm
  · rintro rfl
    intro i
    have same : (Coordinate.index .nil : Fin scalar.volume) = i :=
      Subsingleton.elim (α := Fin 1) _ _
    simpa only [if_pos same] using Value.getElem_fill scalar value i.isLt

/-- Literal-one assignment needs no scalar arithmetic or input access. -/
theorem period_executes (period : Ref outputs scalar)
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs)
    (iterators : IteratorEnv bounds) (before after : Env α outputs) :
    (Statement.assign period .nil (.literal .one)).Executes step zero one input
      iterators before after ↔ Env.Updates before period (Value.fill scalar one) after := by
  simp only [Statement.Executes, Subscripts.eval]
  constructor
  · rintro ⟨value, tensor, evaluated, written, frame⟩
    cases evaluated
    obtain rfl := (scalar_write_iff _ _ _).mp written
    exact frame
  · intro frame
    exact ⟨one, Value.fill scalar one, .literal .one,
      (scalar_write_iff _ _ _).mpr rfl, frame⟩

/-- Different ranks already enforce distinct slots, even at equal volumes. -/
theorem target_separation (vector : Ref outputs ⟨[extent]⟩)
    (matrix : Ref outputs (matrixShape rows cols)) (period : Ref outputs scalar) :
    Ref.position vector ≠ Ref.position matrix ∧
    Ref.position vector ≠ Ref.position period ∧
    Ref.position matrix ≠ Ref.position period := by
  constructor
  · intro same
    obtain ⟨shapeEq, _⟩ := Ref.position_agrees matrix vector same
    have rankEq := congrArg (fun s : Shape => s.dimensions.length) shapeEq
    simp [matrixShape] at rankEq
  constructor
  · intro same
    obtain ⟨shapeEq, _⟩ := Ref.position_agrees period vector same
    have rankEq := congrArg (fun s : Shape => s.dimensions.length) shapeEq
    simp [scalar] at rankEq
  · intro same
    obtain ⟨shapeEq, _⟩ := Ref.position_agrees period matrix same
    have rankEq := congrArg (fun s : Shape => s.dimensions.length) shapeEq
    simp [matrixShape, scalar] at rankEq

/-- Independent observations and full frame; no statement or evaluator occurs. -/
def Initializes (vector : Ref outputs ⟨[extent]⟩)
    (matrix : Ref outputs (matrixShape rows cols)) (period : Ref outputs scalar)
    (zero one : α) (before after : Env α outputs) : Prop :=
  after vector = Value.fill ⟨[extent]⟩ zero ∧
  after matrix = Value.fill (matrixShape rows cols) zero ∧
  after period = Value.fill scalar one ∧
  ∀ {shape} (other : Ref outputs shape),
    Ref.position other ≠ Ref.position vector →
    Ref.position other ≠ Ref.position matrix →
    Ref.position other ≠ Ref.position period → after other = before other

/-- Exact ordered whole-shaped updates, not an execution definition. -/
def updated (vector : Ref outputs ⟨[extent]⟩)
    (matrix : Ref outputs (matrixShape rows cols)) (period : Ref outputs scalar)
    (zero one : α) (before : Env α outputs) : Env α outputs :=
  Env.update (Env.update (Env.update before vector (Value.fill ⟨[extent]⟩ zero))
    matrix (Value.fill (matrixShape rows cols) zero)) period (Value.fill scalar one)

theorem initializes_iff_update (vector : Ref outputs ⟨[extent]⟩)
    (matrix : Ref outputs (matrixShape rows cols)) (period : Ref outputs scalar)
    (zero one : α) (before after : Env α outputs) :
    Initializes vector matrix period zero one before after ↔
      @after = @updated outputs extent rows cols α vector matrix period zero one before := by
  obtain ⟨vm, vp, mp⟩ := target_separation vector matrix period
  have initialized : Initializes vector matrix period zero one before
      (updated vector matrix period zero one before) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [updated, Env.update_other _ _ _ _ vp,
        Env.update_other _ _ _ _ vm, Env.update_same]
    · simp only [updated, Env.update_other _ _ _ _ mp, Env.update_same]
    · exact Env.update_same _ _ _
    · intro shape other ov om op
      simp only [updated, Env.update_other _ _ _ _ op,
        Env.update_other _ _ _ _ om, Env.update_other _ _ _ _ ov]
  constructor
  · intro result
    funext shape other
    by_cases ov : Ref.position other = Ref.position vector
    · obtain ⟨sameShape, sameRef⟩ := Ref.position_agrees vector other ov
      cases sameShape
      cases sameRef
      exact result.1.trans initialized.1.symm
    by_cases om : Ref.position other = Ref.position matrix
    · obtain ⟨sameShape, sameRef⟩ := Ref.position_agrees matrix other om
      cases sameShape
      cases sameRef
      exact result.2.1.trans initialized.2.1.symm
    by_cases op : Ref.position other = Ref.position period
    · obtain ⟨sameShape, sameRef⟩ := Ref.position_agrees period other op
      cases sameShape
      cases sameRef
      exact result.2.2.1.trans initialized.2.2.1.symm
    exact (result.2.2.2 other ov om op).trans (initialized.2.2.2 other ov om op).symm
  · rintro rfl
    exact initialized

/-- Exact ordered store result for arbitrary partial/nondeterministic arithmetic,
arbitrary old values, and every natural extent (including zero). -/
theorem body_executes_iff_update (vector : Ref outputs ⟨[extent]⟩)
    (matrix : Ref outputs (matrixShape rows cols)) (period : Ref outputs scalar)
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs)
    (iterators : IteratorEnv bounds) (before after : Env α outputs) :
    (body vector matrix period).Executes step zero one input iterators before after ↔
      @after = @updated outputs extent rows cols α vector matrix period zero one before := by
  change (∃ middle, (VectorClear.clearVector vector).Executes step zero one input
      iterators before middle ∧ ∃ next,
      (MatrixBodies.clearMatrix matrix).Executes step zero one input iterators middle next ∧
      (Statement.assign period .nil (.literal .one)).Executes step zero one input
        iterators next after) ↔ _
  simp only [VectorClear.clear_vector_executes_iff_update,
    MatrixBodies.clear_matrix_executes, period_executes, Env.update_correct,
    exists_eq_left]
  rfl

/-- Independent complete-store semantics of the composed core body. -/
theorem body_executes_iff (vector : Ref outputs ⟨[extent]⟩)
    (matrix : Ref outputs (matrixShape rows cols)) (period : Ref outputs scalar)
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs)
    (iterators : IteratorEnv bounds) (before after : Env α outputs) :
    (body vector matrix period).Executes step zero one input iterators before after ↔
      Initializes vector matrix period zero one before after :=
  (body_executes_iff_update vector matrix period step zero one input iterators before after).trans
    (initializes_iff_update vector matrix period zero one before after).symm

end Rumoca.GALEC.InitializationBodies
