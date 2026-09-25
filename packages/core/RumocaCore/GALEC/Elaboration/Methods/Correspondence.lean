import RumocaCore.GALEC.Elaboration.Methods.Preparation

/-! Original-method execution and metadata agreement, independent of any block
interface profile. These proofs do not grant source write permissions. -/
namespace Rumoca.GALEC.Elaboration.Methods.Correspondence
open Rumoca.Tensor Rumoca.Solve.Tensor

/-- The returned header method is the very method whose original body was
lowered, not another method with a similar name or body. -/
theorem selected_execution
    (prepared : Methods.Preparation.Prepares name role ceiling block result)
    (selected : Methods.Headers.Selects name block.methods method) :
    ∀ {α : Type} (step : BinaryOp → α → α → α → Prop) (zero one : α)
      (input : Env α (Layout.inputShapes result.1)) (env : IteratorEnv [])
      (before after : Env α (Layout.outputShapes result.1)),
      Bodies.Source.statements (Layout.bindings result.1)
        (Declarations.ShapeLookup.HasShape ceiling block.declarations) ceiling step zero one
        @input .nil @env method.body @before @after ↔
        result.2.Executes step zero one @input @env @before @after := by
  obtain ⟨original, chosen, execution⟩ := Methods.Preparation.prepared_execution prepared
  have equal : original = method := Option.some.inj
    (((Methods.Headers.select_iff _ _ _).mpr chosen).symm.trans
      ((Methods.Headers.select_iff _ _ _).mpr selected))
  subst original
  exact @execution

/-- The same selected method under execution with error signals. -/
theorem selected_runs
    (prepared : Methods.Preparation.Prepares name role ceiling block result)
    (selected : Methods.Headers.Selects name block.methods method) :
    ∀ {α : Type} (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α)
      (input : Env α (Layout.inputShapes result.1)) (env : IteratorEnv [])
      (before after : Signaled α (Layout.outputShapes result.1)),
      Bodies.Source.runs (Layout.bindings result.1)
        (Declarations.ShapeLookup.HasShape ceiling block.declarations) ceiling step finite zero one
        @input .nil @env method.body before after ↔
        result.2.Runs step finite zero one @input @env before after := by
  obtain ⟨original, chosen, execution⟩ := Methods.Preparation.prepared_runs prepared
  have equal : original = method := Option.some.inj
    (((Methods.Headers.select_iff _ _ _).mpr chosen).symm.trans
      ((Methods.Headers.select_iff _ _ _).mpr selected))
  subst original
  exact @execution

/-- The selected method's signal interface is its exposed set. -/
theorem selected_exposes
    (prepared : Methods.Preparation.Prepares name role ceiling block result)
    (selected : Methods.Headers.Selects name block.methods method) :
    ∃ exposed, Reach.Exposes method exposed := by
  obtain ⟨original, exposed, chosen, exposes⟩ := Methods.Preparation.prepared_exposes prepared
  have equal : original = method := Option.some.inj
    (((Methods.Headers.select_iff _ _ _).mpr chosen).symm.trans
      ((Methods.Headers.select_iff _ _ _).mpr selected))
  subst original
  exact ⟨exposed, exposes⟩

/-- Different method capabilities change roles, not the source metadata.
This does not yet supply a state transport or sequential lifecycle theorem. -/
theorem prepared_metadata_eq
    (first : Methods.Preparation.Prepares firstName firstRole ceiling block firstResult)
    (second : Methods.Preparation.Prepares secondName secondRole ceiling block secondResult) :
    firstResult.1.map Layout.Field.declaration = secondResult.1.map Layout.Field.declaration := by
  have firstRead := (Declarations.Real.readAll_iff _ _ _).mpr
    (Methods.Preparation.prepared_declarations first)
  have secondRead := (Declarations.Real.readAll_iff _ _ _).mpr
    (Methods.Preparation.prepared_declarations second)
  exact Option.some.inj (firstRead.symm.trans secondRead)

end Rumoca.GALEC.Elaboration.Methods.Correspondence
