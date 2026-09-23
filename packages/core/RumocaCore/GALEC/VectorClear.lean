import RumocaCore.GALEC.VectorBodies

/-! Rank-one clearing by an existing typed bounded statement. This is a core
execution prerequisite, not a Startup permission or source-admission rule. -/
namespace Rumoca.GALEC.VectorClear
open Rumoca.Tensor Rumoca.Solve.Tensor VectorBodies

/-- One loop body, independent of the extent; no input read or scalar arithmetic. -/
def clearVector (target : Ref outputs ⟨[extent]⟩) : Statement inputs outputs bounds :=
  .bounded extent (.assign target vectorSubscripts (.literal .zero))

theorem clear_cell_executes (target : Ref outputs ⟨[extent]⟩)
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs)
    (iterators : IteratorEnv bounds) (i : Fin extent) (before after : Env α outputs) :
    (Statement.assign target vectorSubscripts (.literal .zero)).Executes step zero one input
      (iterators.push i) before after ↔
    ∃ tensor, TensorWrites.Writes (before target) (vectorIndex i) zero tensor ∧
      Env.Updates before target tensor after := by
  simp only [Statement.Executes, vectorSubscripts, Subscripts.eval, IndexTerm.eval,
    IteratorEnv.push, vectorIndex]
  constructor
  · rintro ⟨result, tensor, evaluated, written, frame⟩
    cases evaluated
    exact ⟨tensor, written, frame⟩
  · rintro ⟨tensor, written, frame⟩
    exact ⟨zero, tensor, .literal .zero, written, frame⟩

/-- The existing full overwrite iteration realizes a constant shaped value. -/
theorem overwrite_constant_eq_fill (zero : α) (initial : Value α shape) :
    TensorWrites.overwrite (fun _ => zero) initial = Value.fill shape zero := by
  apply Value.ext
  intro i hi
  exact (TensorWrites.overwrite_get (fun _ => zero) initial ⟨i, hi⟩).trans
    (Value.getElem_fill shape zero hi).symm

theorem tensor_clear_executes (zero : α) (before after : Value α ⟨[extent]⟩) :
    Iteration.Executes
      (fun (i : Fin extent) first last => TensorWrites.Writes first (vectorIndex i) zero last)
      extent before after ↔ after = Value.fill ⟨[extent]⟩ zero := by
  simp only [vectorIndex_reindex]
  have reindexed := (Iteration.executes_reindex
    (by simp [Shape.volume] : (Shape.mk [extent]).volume = extent)
    (fun i first last => TensorWrites.Writes first i zero last) before after).symm
  exact reindexed.trans ((TensorWrites.overwrite_executes (fun _ => zero) before after).trans
    (by rw [overwrite_constant_eq_fill]))

/-- Exact complete-store frame, for any scalar type and any partial or
nondeterministic arithmetic relation. Even an empty extent is covered. -/
theorem clear_vector_executes (target : Ref outputs ⟨[extent]⟩)
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs)
    (iterators : IteratorEnv bounds) (before after : Env α outputs) :
    (clearVector target).Executes step zero one input iterators before after ↔
    Env.Updates before target (Value.fill ⟨[extent]⟩ zero) after := by
  change Iteration.Executes (σ := Env α outputs) (fun i current next =>
    (Statement.assign target vectorSubscripts (.literal .zero)).Executes step zero one input
      (iterators.push i) current next) extent @before @after ↔ _
  simp_rw [clear_cell_executes]
  rw [StoreIteration.executes_iff target
    (fun i first last => TensorWrites.Writes first (vectorIndex i) zero last)
    extent before after]
  simp only [tensor_clear_executes, exists_eq_left]

/-- Equality to the exact whole-shaped store update; no precondition on the
old destination values or on arithmetic execution. -/
theorem clear_vector_executes_iff_update (target : Ref outputs ⟨[extent]⟩)
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs)
    (iterators : IteratorEnv bounds) (before after : Env α outputs) :
    (clearVector target).Executes step zero one input iterators before after ↔
    @after = @Env.update α outputs ⟨[extent]⟩ before target (Value.fill ⟨[extent]⟩ zero) :=
  (clear_vector_executes target step zero one input iterators before after).trans
    (Env.update_correct before target (Value.fill ⟨[extent]⟩ zero) after)

end Rumoca.GALEC.VectorClear
