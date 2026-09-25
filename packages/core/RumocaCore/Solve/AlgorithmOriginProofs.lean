import RumocaCore.Solve.Algorithm
import RumocaCore.GALEC.TraceProofs
import RumocaCore.GALEC.Elaboration.Scalar.State

/-! Source correspondence for every prepared algorithm model, including ones
constructed independently of `prepare`. -/
namespace Rumoca.Solve.Algorithm
open _root_.Parser.Provenance (Ref Node TracesTo)
open GALEC.UnitOrigins (Field)

private theorem ref_ext {table : _root_.Parser.Provenance.Table Site Rule}
    (left right : Ref table) (same : left.index.val = right.index.val) : left = right := by
  cases left with
  | mk left =>
    cases right with
    | mk right => exact congrArg Ref.mk (Fin.ext same)

theorem Model.state_origin (model : Model source) :
    model.origins.table.get model.origins.references.stateDeclaration =
      .source (model.dae.flat.context.site .declaration) := by
  have same := ref_ext model.origins.references.stateDeclaration
    (model.origins.extension.ref
      (model.dae.origins.extension.ref model.dae.flat.origins.declaration))
    model.origins.correct.1
  rw [same, model.origins.extension.lookup, model.dae.origins.extension.lookup]
  exact model.dae.flat.origins.declaration_source

private theorem Model.field_parent (model : Model source) (field : Field)
    {site : _root_.Parser.Provenance.SourceRef model.dae.flat.context.input.inputs}
    (parent : Ref model.origins.table)
    (member : parent.index.val ∈ (model.origins.references.expected model.dae field).parents)
    (trace : TracesTo model.origins.table parent site) :
    TracesTo model.origins.table (model.origins.references.origin field) site := by
  apply TracesTo.parent (parent := parent) _ trace
  rw [model.origins.correct.2 field]
  exact member

theorem Model.initial_ancestry (model : Model source) :
    TracesTo model.origins.table (model.origins.references.origin .initial)
      (model.dae.flat.context.site .declaration) := by
  apply model.field_parent .initial (model.origins.references.origin .fallback)
  · simp [GALEC.UnitOrigins.References.expected, Node.parents]
  · apply model.field_parent .fallback (model.origins.extension.ref model.dae.initializationOrigin)
    · simp [GALEC.UnitOrigins.References.expected, Node.parents,
        _root_.Parser.Provenance.Table.Extension.ref]
    · exact .source ((model.origins.extension.lookup _).trans model.dae.initialization_origin)

theorem Model.step_ancestry (model : Model source) :
    TracesTo model.origins.table (model.origins.references.origin .addition)
      (model.dae.flat.context.site .equation) := by
  apply model.field_parent .addition
    (model.origins.extension.ref model.dae.origins.expression.root)
  · simp [GALEC.UnitOrigins.References.expected, Node.parents,
      _root_.Parser.Provenance.Table.Extension.ref]
  · exact model.dae.residual_ancestry.extend model.origins.extension

theorem Model.model_ancestry (model : Model source) :
    TracesTo model.origins.table (model.origins.references.origin .model)
      (model.dae.flat.context.site .model) := by
  apply model.field_parent .model
    (model.origins.extension.ref (model.dae.origins.extension.ref model.dae.flat.origins.model))
  · simp [GALEC.UnitOrigins.References.expected, Node.parents,
      _root_.Parser.Provenance.Table.Extension.ref]
  · exact .source ((model.origins.extension.lookup _).trans
      ((model.dae.origins.extension.lookup _).trans model.dae.flat.origins.model_source))

theorem Model.period_ancestry (model : Model source) :
    TracesTo model.origins.table (model.origins.references.origin .periodValue)
      (model.dae.flat.context.site .model) := by
  apply model.field_parent .periodValue (model.origins.references.origin .periodDeclaration)
  · simp [GALEC.UnitOrigins.References.expected, Node.parents]
  · apply model.field_parent .periodDeclaration (model.origins.references.origin .model)
    · simp [GALEC.UnitOrigins.References.expected, Node.parents]
    · exact model.model_ancestry

theorem Model.state_access_ancestry (model : Model source) (field : Field)
    (access : field = .startupTarget ∨ field = .stepRead ∨ field = .stepTarget) :
    TracesTo model.origins.table (model.origins.references.origin field)
      (model.dae.flat.context.site .stateName) := by
  let parent := model.origins.extension.ref
    (model.dae.origins.extension.ref model.dae.flat.origins.state)
  apply model.field_parent field parent
  · rcases access with rfl | rfl | rfl <;>
      simp [GALEC.UnitOrigins.References.expected, parent, Node.parents,
        _root_.Parser.Provenance.Table.Extension.ref]
  · exact .source ((model.origins.extension.lookup _).trans
      ((model.dae.origins.extension.lookup _).trans model.dae.flat.origins.state_source))

/-- The profile equality changes only the index of the actual block trace. -/
def Model.TraceCorrect (model : Model source) : Prop :=
  GALEC.UnitOrigins.TraceCorrect model.dae (model.profile ▸ model.trace)

theorem Model.trace_correct (model : Model source) : model.TraceCorrect := by
  rcases model with ⟨dae, origins, block, profile⟩
  cases profile
  exact origins.references.trace_correct dae origins.correct
    (Model.state_origin ⟨dae, origins, unitBlock, rfl⟩)

/-- One composed guarantee for the actual prepared model: original source
execution of every block that prepares to the scalar results is the lifecycle
execution of `model.block`, and every operation/operand origin of that block
is the required one. -/
theorem Model.preparation_preserves (model : Model source)
    (prepared : GALEC.Elaboration.Block.Prepares ceiling parsed
      (GALEC.Elaboration.Scalar.preparedResult stateName clockName selection))
    (step : Tensor.BinaryOp → α → α → α → Prop) (zero one : α) (add : α → α → α)
    (arithmetic : ∀ x result, step .add x one result ↔ result = add x one)
    (method : GALEC.Method) (before after : GALEC.UnitProfile.State α) :
    (GALEC.Elaboration.Scalar.StateBridge.SourceExec parsed stateName clockName ceiling
        step zero one method before after ↔
      after = GALEC.UnitProfile.solveExecute model.block zero one add method before) ∧
    (model.profile ▸ model.trace).startup.events =
      [.fill (model.origins.references.origin .initial),
        .ret (model.origins.references.origin .startupAssignment)
          (model.origins.references.origin .initial)] ∧
    (model.profile ▸ model.trace).recalibrate.events =
      [.ret (model.origins.references.origin .recalibrate)
        model.origins.references.stateDeclaration] ∧
    (model.profile ▸ model.trace).doStep.events =
      [.fill (model.origins.references.origin .increment),
        .add (model.origins.references.origin .addition)
          (model.origins.references.origin .stepRead)
          (model.origins.references.origin .increment),
        .ret (model.origins.references.origin .stepAssignment)
          (model.origins.references.origin .addition)] ∧
    (model.profile ▸ model.trace).period.events =
      [.fill (model.origins.references.origin .periodValue),
        .ret (model.origins.references.origin .periodAssignment)
          (model.origins.references.origin .periodValue)] ∧
    model.TraceCorrect := by
  refine ⟨?_, ?_⟩
  · rw [model.profile]
    exact GALEC.Elaboration.Scalar.StateBridge.sourceExec_iff_solve prepared step zero one add
      arithmetic method before after
  · rcases model with ⟨dae, origins, block, profile⟩
    cases profile
    exact ⟨rfl, rfl, rfl, rfl, Model.trace_correct ⟨dae, origins, unitBlock, rfl⟩⟩

end Rumoca.Solve.Algorithm
