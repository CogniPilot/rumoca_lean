import RumocaCore.GALEC.Elaboration.Initialization.VectorClear
import RumocaCore.GALEC.InitializationBodies
import RumocaCore.GALEC.Elaboration.Square.Execution

/-! Proposed Startup source body through generic lowering. Writable bindings are
explicit premises, not a claimed normative Startup permission policy. -/
namespace Rumoca.GALEC.Elaboration.Initialization.Body
open Elaboration Elaboration.Surface Rumoca.Tensor Rumoca.Solve.Tensor
open StatementRelations

def periodSource (name : String) : AST.Statement :=
  .assign (stateReference name []) (.literal (.literal "1.0"))

def source (vectorName matrixName periodName : String) : List AST.Statement :=
  [VectorClear.source vectorName "k", Square.clearSource matrixName, periodSource periodName]

def lowered (vector : Ref outputs ⟨[extent]⟩)
    (matrix : Ref outputs (matrixShape extent extent)) (period : Ref outputs scalar) :
    Statement inputs outputs bounds :=
  .seq (VectorClear.lowered vector)
    (.seq (Square.loweredClear matrix) (.seq (.assign period .nil (.literal .one)) .skip))

theorem period_typed (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (period : Ref outputs scalar)
    (resolved : BindingTable.Resolves table [name] ⟨_, .writable period⟩) :
    Bodies.StatementElaborates table HasShape ceiling names (periodSource name)
      (.assign period .nil (.literal .one)) :=
  .assign (.assign (.writable (reference_typed table names resolved .nil)) .one)

theorem typed (table : BindingTable inputs outputs) (vector : Ref outputs ⟨[extent]⟩)
    (matrix : Ref outputs (matrixShape extent extent)) (period : Ref outputs scalar)
    (vectorBound : BindingTable.Resolves table [vectorName] ⟨_, .writable vector⟩)
    (matrixBound : BindingTable.Resolves table [matrixName] ⟨_, .writable matrix⟩)
    (periodBound : BindingTable.Resolves table [periodName] ⟨_, .writable period⟩)
    (vectorKnown : HasShape [vectorName] ⟨[extent]⟩)
    (matrixKnown : HasShape [matrixName] (matrixShape extent extent))
    (positive : 0 < extent) (within : extent ≤ ceiling) (axisBound : 2 ≤ ceiling) :
    Bodies.BodyElaborates table HasShape ceiling .nil (source vectorName matrixName periodName)
      (lowered vector matrix period) :=
  .cons (VectorClear.typed table .nil vector vectorBound vectorKnown positive within .nil)
    (.cons (Square.clear_typed table .nil matrix matrixBound matrixKnown positive within axisBound .nil .nil)
      (.cons (period_typed table .nil period periodBound) .nil))

theorem lower (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (vector : Ref outputs ⟨[extent]⟩)
    (matrix : Ref outputs (matrixShape extent extent)) (period : Ref outputs scalar)
    (vectorBound : BindingTable.Resolves table [vectorName] ⟨_, .writable vector⟩)
    (matrixBound : BindingTable.Resolves table [matrixName] ⟨_, .writable matrix⟩)
    (periodBound : BindingTable.Resolves table [periodName] ⟨_, .writable period⟩)
    (vectorKnown : HasShape [vectorName] ⟨[extent]⟩)
    (matrixKnown : HasShape [matrixName] (matrixShape extent extent))
    (positive : 0 < extent) (within : extent ≤ ceiling) (axisBound : 2 ≤ ceiling) :
    Bodies.statements table lookupShape ceiling .nil (source vectorName matrixName periodName) =
      some (lowered vector matrix period) :=
  Bodies.statements_complete table lookupShape HasShape correct ceiling .nil _ _
    (typed table vector matrix period vectorBound matrixBound periodBound vectorKnown matrixKnown
      positive within axisBound)

theorem equivalent (vector : Ref outputs ⟨[extent]⟩)
    (matrix : Ref outputs (matrixShape extent extent)) (period : Ref outputs scalar)
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs) :
    Equivalent step zero one @input (bounds := bounds)
      (lowered vector matrix period) (Rumoca.GALEC.InitializationBodies.body vector matrix period) :=
  seq_congr step zero one @input (VectorClear.equivalent vector step zero one @input)
    (seq_congr step zero one @input (Square.clear_equivalent matrix step zero one @input)
      (seq_skip_right step zero one @input _))

theorem source_executes (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (vector : Ref outputs ⟨[extent]⟩)
    (matrix : Ref outputs (matrixShape extent extent)) (period : Ref outputs scalar)
    (vectorBound : BindingTable.Resolves table [vectorName] ⟨_, .writable vector⟩)
    (matrixBound : BindingTable.Resolves table [matrixName] ⟨_, .writable matrix⟩)
    (periodBound : BindingTable.Resolves table [periodName] ⟨_, .writable period⟩)
    (vectorKnown : HasShape [vectorName] ⟨[extent]⟩)
    (matrixKnown : HasShape [matrixName] (matrixShape extent extent))
    (positive : 0 < extent) (within : extent ≤ ceiling) (axisBound : 2 ≤ ceiling)
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs)
    (env : IteratorEnv []) (before after : Env α outputs) :
    Bodies.Source.statements table HasShape ceiling step zero one @input .nil @env
      (source vectorName matrixName periodName) @before @after ↔
      Rumoca.GALEC.InitializationBodies.Initializes vector matrix period zero one @before @after :=
  (Bodies.statements_correct table lookupShape HasShape correct ceiling .nil _ _
    (typed table vector matrix period vectorBound matrixBound periodBound vectorKnown matrixKnown
      positive within axisBound) step zero one @input @env @before @after).trans
    ((equivalent vector matrix period step zero one @input @env @before @after).trans
      (Rumoca.GALEC.InitializationBodies.body_executes_iff vector matrix period step zero one
        @input @env @before @after))

end Rumoca.GALEC.Elaboration.Initialization.Body
