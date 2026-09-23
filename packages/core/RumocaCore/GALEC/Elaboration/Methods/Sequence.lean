import RumocaCore.GALEC.Elaboration.Layout.State
import RumocaCore.GALEC.Elaboration.Methods.Correspondence

/-! Sequential composition of two original methods prepared from one block.
The handoff uses the actual first post-store and its unchanged read-only inputs.
The final pair includes read-only values, not only writable observations.
This is relational source/IR composition, not a scheduler or C lifecycle claim. -/
namespace Rumoca.GALEC.Elaboration.Methods.Sequence
open Rumoca.Tensor Rumoca.Solve.Tensor Layout.State

/-- Both original methods are fixed before all runtime values and arithmetic.
The intermediate store is produced by execution, never an unrelated handoff
witness. Full ordered declaration equality comes from the same source block. -/
theorem prepared_sequence
    (first : Methods.Preparation.Prepares firstName firstRole ceiling block firstResult)
    (second : Methods.Preparation.Prepares secondName secondRole ceiling block secondResult) :
    ∃ firstMethod secondMethod,
      Methods.Headers.Selects firstName block.methods firstMethod ∧
      Methods.Headers.Selects secondName block.methods secondMethod ∧
      ∀ {α : Type} (step : BinaryOp → α → α → α → Prop) (zero one : α)
        (env : IteratorEnv [])
        (input : Env α (Layout.inputShapes firstResult.1))
        (before : Env α (Layout.outputShapes firstResult.1))
        (finalInput : Env α (Layout.inputShapes secondResult.1))
        (finalOutput : Env α (Layout.outputShapes secondResult.1)),
        (∃ middle : Env α (Layout.outputShapes firstResult.1),
          Bodies.Source.statements (Layout.bindings firstResult.1)
            (Declarations.ShapeLookup.HasShape ceiling block.declarations) ceiling step zero one
            @input .nil @env firstMethod.body @before @middle ∧
          let next := repartition (Methods.Correspondence.prepared_metadata_eq first second)
            @input @middle
          @next.1 = @finalInput ∧
          Bodies.Source.statements (Layout.bindings secondResult.1)
            (Declarations.ShapeLookup.HasShape ceiling block.declarations) ceiling step zero one
            next.1 .nil @env secondMethod.body next.2 @finalOutput) ↔
        (∃ middle : Env α (Layout.outputShapes firstResult.1),
          firstResult.2.Executes step zero one @input @env @before @middle ∧
          let next := repartition (Methods.Correspondence.prepared_metadata_eq first second)
            @input @middle
          @next.1 = @finalInput ∧
          secondResult.2.Executes step zero one next.1 @env next.2 @finalOutput) := by
  obtain ⟨firstMethod, selectedFirst, firstExecution⟩ := Methods.Preparation.prepared_execution first
  obtain ⟨secondMethod, selectedSecond, secondExecution⟩ := Methods.Preparation.prepared_execution second
  refine ⟨firstMethod, secondMethod, selectedFirst, selectedSecond, ?_⟩
  intro α step zero one env input before finalInput finalOutput
  simp only [firstExecution, secondExecution]

/-- The handoff preserves the complete supplied state. Apply this to the
actual post-store in `prepared_sequence`; this lemma alone asserts no execution. -/
theorem prepared_handoff
    (first : Methods.Preparation.Prepares firstName firstRole ceiling block firstResult)
    (second : Methods.Preparation.Prepares secondName secondRole ceiling block secondResult)
    (input : Env α (Layout.inputShapes firstResult.1))
    (post : Env α (Layout.outputShapes firstResult.1))
    (nextInput : Env α (Layout.inputShapes secondResult.1))
    (nextOutput : Env α (Layout.outputShapes secondResult.1)) :
    repartition (Methods.Correspondence.prepared_metadata_eq first second) @input @post =
        (@nextInput, @nextOutput) ↔
      @join α secondResult.1 @nextInput @nextOutput =
        @castEnv (shapes firstResult.1) (shapes secondResult.1) α
          (shapes_aligned (Methods.Correspondence.prepared_metadata_eq first second))
          (join firstResult.1 @input @post) :=
  repartition_iff _ @input @post @nextInput @nextOutput

end Rumoca.GALEC.Elaboration.Methods.Sequence
