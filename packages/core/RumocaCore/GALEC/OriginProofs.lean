import RumocaCore.GALEC.IR

/-! Source correspondence for every admitted GALEC model, including ones
constructed independently of the ordinary lowerer. -/
namespace Rumoca.GALEC
open _root_.Parser.Provenance (Ref Node TracesTo)
open UnitOrigins (Field)

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
  · simp [UnitOrigins.References.expected, Node.parents]
  · apply model.field_parent .fallback (model.origins.extension.ref model.dae.initializationOrigin)
    · simp [UnitOrigins.References.expected, Node.parents,
        _root_.Parser.Provenance.Table.Extension.ref]
    · exact .source ((model.origins.extension.lookup _).trans model.dae.initialization_origin)

theorem Model.step_ancestry (model : Model source) :
    TracesTo model.origins.table (model.origins.references.origin .addition)
      (model.dae.flat.context.site .equation) := by
  apply model.field_parent .addition
    (model.origins.extension.ref model.dae.origins.expression.root)
  · simp [UnitOrigins.References.expected, Node.parents,
      _root_.Parser.Provenance.Table.Extension.ref]
  · exact model.dae.residual_ancestry.extend model.origins.extension

theorem Model.model_ancestry (model : Model source) :
    TracesTo model.origins.table (model.origins.references.origin .model)
      (model.dae.flat.context.site .model) := by
  apply model.field_parent .model
    (model.origins.extension.ref (model.dae.origins.extension.ref model.dae.flat.origins.model))
  · simp [UnitOrigins.References.expected, Node.parents,
      _root_.Parser.Provenance.Table.Extension.ref]
  · exact .source ((model.origins.extension.lookup _).trans
      ((model.dae.origins.extension.lookup _).trans model.dae.flat.origins.model_source))

theorem Model.period_ancestry (model : Model source) :
    TracesTo model.origins.table (model.origins.references.origin .periodValue)
      (model.dae.flat.context.site .model) := by
  apply model.field_parent .periodValue (model.origins.references.origin .periodDeclaration)
  · simp [UnitOrigins.References.expected, Node.parents]
  · apply model.field_parent .periodDeclaration (model.origins.references.origin .model)
    · simp [UnitOrigins.References.expected, Node.parents]
    · exact model.model_ancestry

theorem Model.state_access_ancestry (model : Model source) (field : Field)
    (access : field = .startupTarget ∨ field = .stepRead ∨ field = .stepTarget) :
    TracesTo model.origins.table (model.origins.references.origin field)
      (model.dae.flat.context.site .stateName) := by
  let parent := model.origins.extension.ref
    (model.dae.origins.extension.ref model.dae.flat.origins.state)
  apply model.field_parent field parent
  · rcases access with rfl | rfl | rfl <;>
      simp [UnitOrigins.References.expected, parent, Node.parents,
        _root_.Parser.Provenance.Table.Extension.ref]
  · exact .source ((model.origins.extension.lookup _).trans
      ((model.dae.origins.extension.lookup _).trans model.dae.flat.origins.state_source))

end Rumoca.GALEC
