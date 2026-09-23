import RumocaCore.GALEC.Elaboration.Square.Lowering
import RumocaCore.GALEC.StatementRelations

/-! Relate the exact result of generic surface lowering to the already proved
prepared square/AD body. Only skip/sequence/loop congruence is used; no arithmetic
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

/-- Universal successful lowering, not an example evaluation. Bindings and
source-shape meanings are explicit independent premises. -/
theorem square_lowered (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
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
    Bodies.statements table lookupShape ceiling .nil (squareSource inputName rhsName jacobianName) =
      some (loweredSquare source rhs jacobian) :=
  Bodies.statements_complete table lookupShape HasShape correct ceiling .nil _ _
    (square_typed table source rhs jacobian inputBound rhsBound jacobianBound inputKnown
      jacobianKnown positive within axisBound)

/-- Actual surface-AST source execution iff the prepared body, retaining the
original finite primal domain when later instantiated with finite arithmetic. -/
theorem square_source_executes (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
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
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs)
    (env : IteratorEnv []) (before after : Env α outputs) :
    Bodies.Source.statements table HasShape ceiling step zero one @input .nil @env
      (squareSource inputName rhsName jacobianName) @before @after ↔
      (SquareBodies.body source rhs jacobian).Executes step zero one @input @env @before @after :=
  (Bodies.statements_correct table lookupShape HasShape correct ceiling .nil _ _
    (square_typed table source rhs jacobian inputBound rhsBound jacobianBound inputKnown
      jacobianKnown positive within axisBound) step zero one @input @env @before @after).trans
    (square_equivalent source rhs jacobian step zero one @input @env @before @after)

end Rumoca.GALEC.Elaboration.Square
