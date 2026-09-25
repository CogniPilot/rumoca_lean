import RumocaCore.GALEC.Elaboration.Square.Lowering
import RumocaCore.GALEC.StatementRelations

/-! Relate the exact result of generic surface lowering to the already proved
prepared square/AD body, and lower the checked DoStep body that guards it. Only skip/sequence/loop congruence is used; no arithmetic
rewrite or source-body recognizer replaces the actual lowered statement. -/
namespace Rumoca.GALEC.Elaboration.Square
open StatementRelations
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor Coefficients VectorBodies

theorem pointwise_equivalent (source : Ref inputs ⟨[extent]⟩) (rhs : Ref outputs ⟨[extent]⟩)
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs) :
    Equivalent step zero one @input (bounds := bounds)
      (loweredPointwise source rhs) (pointwise source rhs squaredInput) :=
  bounded_congr step zero one @input extent (seq_skip_right step zero one @input _)

theorem scatter_equivalent (source : Ref inputs ⟨[extent]⟩)
    (jacobian : Ref outputs (matrixShape extent extent))
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs) :
    Equivalent step zero one @input (bounds := bounds)
      (loweredScatter source jacobian) (scatter source jacobian doubledInput) :=
  bounded_congr step zero one @input extent (seq_skip_right step zero one @input _)

theorem clear_equivalent (jacobian : Ref outputs (matrixShape extent extent))
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs) :
    Equivalent step zero one @input (bounds := bounds)
      (loweredClear jacobian) (MatrixBodies.clearMatrix jacobian) :=
  bounded_congr step zero one @input extent
    ((seq_skip_right step zero one @input _).trans
      (bounded_congr step zero one @input extent (seq_skip_right step zero one @input _)))

theorem square_equivalent (source : Ref inputs ⟨[extent]⟩) (rhs : Ref outputs ⟨[extent]⟩)
    (jacobian : Ref outputs (matrixShape extent extent))
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs) :
    Equivalent step zero one @input (bounds := bounds)
      (loweredSquare source rhs jacobian) (SquareBodies.body source rhs jacobian) :=
  seq_congr step zero one @input (pointwise_equivalent source rhs step zero one @input)
    (seq_congr step zero one @input (clear_equivalent jacobian step zero one @input)
      ((seq_skip_right step zero one @input _).trans
        (scatter_equivalent source jacobian step zero one @input)))

/-- Universal successful lowering of the checked DoStep body, not an example
evaluation. Bindings and source-shape meanings are explicit independent premises. -/
theorem checked_lowered (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (source : Ref inputs ⟨[extent]⟩) (rhs : Ref outputs ⟨[extent]⟩)
    (jacobian : Ref outputs (matrixShape extent extent))
    (inputBound : BindingTable.Resolves table [inputName] ⟨_, .readOnly source⟩)
    (rhsBound : BindingTable.Resolves table [rhsName] ⟨_, .writable rhs⟩)
    (jacobianBound : BindingTable.Resolves table [jacobianName] ⟨_, .writable jacobian⟩)
    (inputKnown : HasShape [inputName] ⟨[extent]⟩)
    (jacobianKnown : HasShape [jacobianName] (matrixShape extent extent))
    (positive : 0 < extent) (within : extent ≤ ceiling) (axisBound : 2 ≤ ceiling) :
    Bodies.statements table lookupShape ceiling .nil (checkedSource inputName rhsName jacobianName) =
      some (loweredChecked source rhs jacobian) :=
  Bodies.statements_complete table lookupShape HasShape correct ceiling .nil _ _
    (checked_typed table source rhs jacobian inputBound rhsBound jacobianBound inputKnown
      jacobianKnown positive within axisBound)

/-- Actual surface-AST execution with error signals iff the lowered checked
body, for every arithmetic and finiteness interpretation. -/
theorem checked_source_runs (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (source : Ref inputs ⟨[extent]⟩) (rhs : Ref outputs ⟨[extent]⟩)
    (jacobian : Ref outputs (matrixShape extent extent))
    (inputBound : BindingTable.Resolves table [inputName] ⟨_, .readOnly source⟩)
    (rhsBound : BindingTable.Resolves table [rhsName] ⟨_, .writable rhs⟩)
    (jacobianBound : BindingTable.Resolves table [jacobianName] ⟨_, .writable jacobian⟩)
    (inputKnown : HasShape [inputName] ⟨[extent]⟩)
    (jacobianKnown : HasShape [jacobianName] (matrixShape extent extent))
    (positive : 0 < extent) (within : extent ≤ ceiling) (axisBound : 2 ≤ ceiling)
    (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α) (input : Env α inputs)
    (env : IteratorEnv []) (before after : Signaled α outputs) :
    Bodies.Source.runs table HasShape ceiling step finite zero one @input .nil @env
      (checkedSource inputName rhsName jacobianName) before after ↔
      (loweredChecked source rhs jacobian).Runs step finite zero one @input @env before after :=
  Bodies.statements_runs table lookupShape HasShape correct ceiling .nil _ _
    (checked_typed table source rhs jacobian inputBound rhsBound jacobianBound inputKnown
      jacobianKnown positive within axisBound) step finite zero one @input @env before after

end Rumoca.GALEC.Elaboration.Square
