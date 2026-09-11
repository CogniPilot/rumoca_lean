import RumocaCore.IR.Solve

/-! Source ancestry for the actual prepared scalar IVP, including the two
initialization decisions. These proofs use the recorded graph and its rules. -/
namespace Rumoca.Solve
open _root_.Parser.Provenance (Ref Node TracesTo)

theorem Model.initial_ancestry (model : Model source) :
    TracesTo model.origins.table model.origins.initial (model.dae.flat.context.site .declaration) := by
  have source := (model.origins.extension.lookup _).trans model.dae.initialization_origin
  apply TracesTo.parent (parent := model.origins.extension.ref model.dae.initializationOrigin)
    _ (.source source)
  rw [model.origins.initial_correct]
  simp [Node.parents, _root_.Parser.Provenance.Table.Extension.ref]

theorem Model.completion_ancestry (model : Model source) :
    TracesTo model.origins.table model.origins.completion
      (model.dae.flat.context.site .declaration) := by
  apply TracesTo.parent (parent := model.origins.initial) _ model.initial_ancestry
  rw [model.origins.completion_correct]
  simp [Node.parents]

theorem Model.notice_ancestry (model : Model source) (notice : Initialization.Notice) :
    TracesTo model.origins.table (model.noticeOrigin notice)
      (model.dae.flat.context.site .declaration) := by
  cases notice
  · exact model.initial_ancestry
  · exact model.completion_ancestry

private theorem Program.Origins.unit_ancestry (dae : DAE.Model source)
    {table : Provenance.Table dae.flat.context} (extension : dae.origins.table.Extension table)
    (origin : Program.Origins table program) (correct : origin.Correct dae Fin.elim0)
    (equal : program = unitDerivative) :
    TracesTo table origin.root (dae.flat.context.site .equation) := by
  cases equal
  cases origin with
  | one operator next =>
    apply TracesTo.parent (parent := extension.ref dae.origins.expression.root)
      _ (dae.residual_ancestry.extend extension)
    change (extension.ref dae.origins.expression.root).index.val ∈ (table.get operator).parents
    rw [correct.1]
    simp [Node.parents, _root_.Parser.Provenance.Table.Extension.ref]

theorem Model.derivative_ancestry (model : Model source) :
    TracesTo model.origins.table model.origins.derivative.root
      (model.dae.flat.context.site .equation) :=
  Program.Origins.unit_ancestry model.dae model.origins.extension model.origins.derivative
    model.origins.derivative_correct model.derivative_source

end Rumoca.Solve
