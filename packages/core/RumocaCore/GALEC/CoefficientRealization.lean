import RumocaCore.Solve.Tensor.Diagonal
import RumocaCore.Solve.Tensor.Finite
import RumocaCore.GALEC.TensorWrites

/-! Prepared coefficient realization and shape-preserving loop execution.
There is no parser, mutable aliasing model or emitter API here.
The input is immutable; pointwise evaluation preserves the nominal shape.
Evaluator equality and ordered finite execution are deliberately separate. -/
namespace Rumoca.GALEC.Coefficients
open Rumoca Rumoca.Tensor Rumoca.Solve.Tensor

inductive ScalarExpr where
  | input
  | literal (value : Literal)
  | binary (op : BinaryOp) (left right : ScalarExpr)
  deriving Repr

def ScalarExpr.eval (ops : ScalarOps α) (zero one input : α) : ScalarExpr → α
  | .input => input
  | .literal value => value.eval zero one
  | .binary op left right =>
      op.scalar ops (left.eval ops zero one input) (right.eval ops zero one input)

/-- A value-level map, not compilation by enumeration of tensor elements. -/
def ScalarExpr.pointwise (e : ScalarExpr) (ops : ScalarOps α) (zero one : α)
    (input : Value α shape) : Value α shape :=
  input.mapWith (fun x => e.eval ops zero one x)

theorem ScalarExpr.pointwise_get (e : ScalarExpr) (ops : ScalarOps α) (zero one : α)
    (input : Value α shape) (i : Fin shape.volume) :
    (e.pointwise ops zero one input)[i] = e.eval ops zero one input[i] :=
  Value.getElem_mapWith _ _ i.isLt

/-- This proposition alone makes no claim that any finite instruction executes. -/
structure EvaluatorRealization (p : DiagonalProgram Γ shape) (input : Ref Γ shape)
    (e : ScalarExpr) (ops : ScalarOps α) (zero one : α) : Prop where
  coefficients : ∀ env : Env α Γ,
    p.coefficients.eval ops zero one env = e.pointwise ops zero one (env input)

theorem EvaluatorRealization.diagonal_correct
    {Γ : List Shape} {shape : Shape} {p : DiagonalProgram Γ shape}
    {input : Ref Γ shape} {e : ScalarExpr} {ops : ScalarOps α} {zero one : α}
    (h : EvaluatorRealization p input e ops zero one) (env : Env α Γ)
    (initial : Value α (matrixShape shape.volume shape.volume)) :
    TensorWrites.diagonal zero (e.pointwise ops zero one (env input)) initial =
      p.eval ops zero one env := by
  rw [← h.coefficients env]
  exact TensorWrites.diagonal_prepared p ops zero one env initial

noncomputable section

def ScalarExpr.inDomain (input : Binary64.Value) : ScalarExpr → Prop
  | .input => True
  | .literal _ => True
  | .binary op left right =>
      left.inDomain input ∧ right.inDomain input ∧
      Finite.Domain op (left.eval Finite.ops Binary64.positiveZero Binary64.one input)
        (right.eval Finite.ops Binary64.positiveZero Binary64.one input)

/-- Independent scalar rounding relations reused from ordered Solve execution. -/
inductive ScalarExpr.Executes (input : Binary64.Value) :
    ScalarExpr → Binary64.Value → Prop where
  | input : Executes input .input input
  | literal (value : Literal) : Executes input (.literal value)
      (value.eval Binary64.positiveZero Binary64.one)
  | binary {op left right a b result} :
      Executes input left a → Executes input right b → Finite.Result op a b result →
      Executes input (.binary op left right) result

theorem ScalarExpr.executes_iff (e : ScalarExpr) (input result : Binary64.Value) :
    e.Executes input result ↔ e.inDomain input ∧
      result = e.eval Finite.ops Binary64.positiveZero Binary64.one input := by
  constructor
  · intro h
    induction h with
    | input => exact ⟨trivial, rfl⟩
    | literal value => exact ⟨trivial, rfl⟩
    | binary hl hr step ihl ihr =>
      obtain ⟨hd, he⟩ := (Finite.result_iff _ _ _ _).mp step
      rcases ihl with ⟨dl, rfl⟩
      rcases ihr with ⟨dr, rfl⟩
      exact ⟨⟨dl, dr, hd⟩, he⟩
  · intro h
    induction e generalizing result with
    | input => rcases h with ⟨_, rfl⟩; exact .input
    | literal value => rcases h with ⟨_, rfl⟩; exact .literal value
    | binary op left right ihl ihr =>
      rcases h with ⟨⟨dl, dr, hd⟩, rfl⟩
      exact .binary (ihl _ ⟨dl, rfl⟩) (ihr _ ⟨dr, rfl⟩)
        ((Finite.result_iff _ _ _ _).mpr ⟨hd, rfl⟩)

/-- Evaluate one scalar RHS by independent rounding relations, then write its
result. The immutable scalar input is separate from the mutable destination. -/
def ScalarExpr.Writes (e : ScalarExpr) (input : Binary64.Value)
    (index : Fin target.volume) (before after : Value Binary64.Value target) : Prop :=
  ∃ result, e.Executes input result ∧ TensorWrites.Writes before index result after

theorem ScalarExpr.write_iff (e : ScalarExpr) (input : Binary64.Value)
    (index : Fin target.volume) (before after : Value Binary64.Value target) :
    e.Writes input index before after ↔ e.inDomain input ∧
      after = TensorWrites.write before index
        (e.eval Finite.ops Binary64.positiveZero Binary64.one input) := by
  simp only [Writes, executes_iff, TensorWrites.write_correct]
  constructor
  · rintro ⟨result, ⟨domain, rfl⟩, written⟩
    exact ⟨domain, written⟩
  · rintro ⟨domain, written⟩
    exact ⟨_, ⟨domain, rfl⟩, written⟩

theorem ScalarExpr.scatter_executes_iff (e : ScalarExpr)
    (input : Value Binary64.Value shape)
    (initial final : Value Binary64.Value (matrixShape shape.volume shape.volume)) :
    Iteration.Executes (fun i => e.Writes input[i] (matrixIndex (i, i)))
      shape.volume initial final ↔
    (∀ i : Fin shape.volume, e.inDomain input[i]) ∧
      final = TensorWrites.scatter
        (e.pointwise Finite.ops Binary64.positiveZero Binary64.one input) initial := by
  apply Iteration.run_guarded_correct
  intro i before after
  change e.Writes input[i] (matrixIndex (i, i)) before after ↔ _
  rw [ScalarExpr.pointwise_get]
  exact e.write_iff input[i] (matrixIndex (i, i)) before after

/-- Pointwise RHS execution, with each scalar result checked independently.
The original contents of the shaped destination impose no premise. -/
theorem ScalarExpr.pointwise_executes_iff (e : ScalarExpr)
    (input initial final : Value Binary64.Value shape) :
    Iteration.Executes (fun i => e.Writes input[i] i) shape.volume initial final ↔
      ∀ i : Fin shape.volume, e.Executes input[i] final[i] := by
  rw [Iteration.run_guarded_correct
    (fun i before => TensorWrites.write before i
      (e.eval Finite.ops Binary64.positiveZero Binary64.one input[i]))
    _ (fun i => e.inDomain input[i])
    (fun i before after => e.write_iff input[i] i before after)]
  constructor
  · rintro ⟨domain, rfl⟩
    intro i
    exact (e.executes_iff _ _).mpr ⟨domain i, TensorWrites.overwrite_get _ initial i⟩
  · intro executed
    constructor
    · exact fun i => ((e.executes_iff _ _).mp (executed i)).1
    · apply Value.ext
      intro i hi
      exact ((e.executes_iff _ _).mp (executed ⟨i, hi⟩)).2.trans
        (TensorWrites.overwrite_get
          (fun j => e.eval Finite.ops Binary64.positiveZero Binary64.one input[j])
          initial ⟨i, hi⟩).symm

/-- Two ordered phases: clear the shaped destination, then evaluate and write
each diagonal coefficient. Neither relation invokes the prepared evaluator. -/
def ScalarExpr.Materializes (e : ScalarExpr) (input : Value Binary64.Value shape)
    (initial final : Value Binary64.Value (matrixShape shape.volume shape.volume)) : Prop :=
  ∃ cleared,
    Iteration.Executes (fun i before after =>
      TensorWrites.Writes before i Binary64.positiveZero after)
      (matrixShape shape.volume shape.volume).volume initial cleared ∧
    Iteration.Executes (fun i => e.Writes input[i] (matrixIndex (i, i)))
      shape.volume cleared final

theorem ScalarExpr.materializes_iff (e : ScalarExpr) (input : Value Binary64.Value shape)
    (initial final : Value Binary64.Value (matrixShape shape.volume shape.volume)) :
    e.Materializes input initial final ↔
      (∀ i : Fin shape.volume, e.inDomain input[i]) ∧
      final = TensorWrites.diagonal Binary64.positiveZero
        (e.pointwise Finite.ops Binary64.positiveZero Binary64.one input) initial := by
  simp only [Materializes, TensorWrites.overwrite_executes, scatter_executes_iff]
  constructor
  · rintro ⟨cleared, rfl, domain, written⟩
    exact ⟨domain, written⟩
  · rintro ⟨domain, written⟩
    exact ⟨_, rfl, domain, written⟩

/-- `retained` records ordered source instructions not evaluated by the compact
expression. It cannot be dropped merely because coefficients evaluate equally. -/
structure FiniteRealization (p : DiagonalProgram Γ shape) (input : Ref Γ shape)
    (e : ScalarExpr) (retained : Env Binary64.Value Γ → Prop) : Prop where
  evaluator : EvaluatorRealization p input e Finite.ops Binary64.positiveZero Binary64.one
  domain : ∀ env, Finite.InDomain p.coefficients env ↔
    retained env ∧ ∀ i : Fin shape.volume, e.inDomain (env input)[i]

variable {Γ : List Shape} {shape : Shape} {p : DiagonalProgram Γ shape}
  {input : Ref Γ shape} {e : ScalarExpr} {retained : Env Binary64.Value Γ → Prop}
  {result : Value Binary64.Value shape}

/-- Universal exact execution/result correspondence, retaining the omitted
instruction domain and the scalar expression's own finite execution checks. -/
theorem FiniteRealization.executes_iff
    (h : FiniteRealization p input e retained) (env : Env Binary64.Value Γ)
    (result : Value Binary64.Value shape) :
    Finite.Executes p.coefficients env result ↔
      retained env ∧ ∀ i : Fin shape.volume, e.Executes (env input)[i] result[i] := by
  rw [Finite.executes_iff, h.domain, h.evaluator.coefficients]
  constructor
  · rintro ⟨⟨hr, hd⟩, rfl⟩
    exact ⟨hr, fun i => (ScalarExpr.executes_iff _ _ _).mpr
      ⟨hd i, ScalarExpr.pointwise_get _ _ _ _ _ i⟩⟩
  · rintro ⟨hr, hs⟩
    have point := fun i => (ScalarExpr.executes_iff _ _ _).mp (hs i)
    refine ⟨⟨hr, fun i => (point i).1⟩, ?_⟩
    apply Value.ext
    intro i hi
    exact (point ⟨i, hi⟩).2.trans (ScalarExpr.pointwise_get _ _ _ _ _ ⟨i, hi⟩).symm

theorem FiniteRealization.result_exact
    (h : FiniteRealization p input e retained) (env : Env Binary64.Value Γ)
    (executed : Finite.Executes p.coefficients env result) :
    result = e.pointwise Finite.ops Binary64.positiveZero Binary64.one (env input) :=
  (Finite.executes_sound executed).2.trans (h.evaluator.coefficients env)

/-- Composition keeps the original ordered program domain as well as exact
matrix results. A compact coefficient expression alone cannot erase it. -/
theorem FiniteRealization.materializes_iff
    (h : FiniteRealization p input e retained) (env : Env Binary64.Value Γ)
    (initial final : Value Binary64.Value (matrixShape shape.volume shape.volume)) :
    (retained env ∧ e.Materializes (env input) initial final) ↔
      Finite.InDomain p.coefficients env ∧
        final = p.eval Finite.ops Binary64.positiveZero Binary64.one env := by
  rw [ScalarExpr.materializes_iff, h.evaluator.diagonal_correct, h.domain]
  exact and_assoc.symm

end
end Rumoca.GALEC.Coefficients
