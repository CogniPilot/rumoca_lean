import RumocaCore.Solve.FMI3
import RumocaCore.Provenance.Lowering

/-! The actual prepared IVP preserves Solve values and complete occurrence
provenance. These are preparation contracts, not FMI ABI or printer-map proofs. -/
namespace Rumoca.Solve
open _root_.Parser.Provenance (Ref Node TracesTo)
open FMI3Origins (Field References)

/-- A role's semantic source anchor, independent of the graph builder. -/
def FMI3Origins.Field.sourceField : Field → Rumoca.Origins.Field
  | .model | .input | .time => .model
  | .observation | .derivativeName | .outputReturn | .outputRead => .stateName
  | .policy | .derivativeFill | .derivativeReturn | .derivativeRead => .equation
  | .initialFill | .initialReturn | .initialRead => .declaration

theorem FMI3Model.source_origin (model : FMI3Model source) (field : Rumoca.Origins.Field) :
    model.origins.table.get (model.origins.references.sourceOrigin field) =
      .source (model.solve.dae.flat.context.site field) := by
  have same : model.origins.references.sourceOrigin field =
      model.origins.extension.ref (model.solve.sourceOrigin field) := by
    apply congrArg Ref.mk
    exact Fin.ext (model.origins.correct.1 field)
  rw [same, model.origins.extension.lookup]
  exact model.solve.source_origin field

private theorem FMI3Model.field_parent (model : FMI3Model source) (field : Field)
    {site : _root_.Parser.Provenance.SourceRef model.solve.dae.flat.context.input.inputs}
    (parent : Ref model.origins.table)
    (member : parent.index.val ∈ (model.origins.references.expected model.solve field).parents)
    (trace : TracesTo model.origins.table parent site) :
    TracesTo model.origins.table (model.origins.references.origin field) site := by
  apply TracesTo.parent (parent := parent) _ trace
  rw [model.origins.correct.2 field]
  exact member

theorem FMI3Model.origin_ancestry (model : FMI3Model source) (field : Field) :
    TracesTo model.origins.table (model.origins.references.origin field)
      (model.solve.dae.flat.context.site field.sourceField) := by
  have sourceTrace (field : Rumoca.Origins.Field) :
      TracesTo model.origins.table
        (model.origins.extension.ref (model.solve.sourceOrigin field))
        (model.solve.dae.flat.context.site field) :=
    .source ((model.origins.extension.lookup _).trans (model.solve.source_origin field))
  have modelTrace : TracesTo model.origins.table (model.origins.references.origin .model)
      (model.solve.dae.flat.context.site .model) := by
    apply model.field_parent .model
      (model.origins.extension.ref (model.solve.sourceOrigin .model)) _ (sourceTrace .model)
    simp [References.expected, Node.parents, _root_.Parser.Provenance.Table.Extension.ref]
  have initialTrace : TracesTo model.origins.table (model.origins.references.origin .initialFill)
      (model.solve.dae.flat.context.site .declaration) := by
    apply model.field_parent .initialFill
      (model.origins.extension.ref model.solve.origins.completion)
      _ (model.solve.completion_ancestry.extend model.origins.extension)
    simp [References.expected, Node.parents, _root_.Parser.Provenance.Table.Extension.ref]
  have derivativeTrace : TracesTo model.origins.table
      (model.origins.references.origin .derivativeFill)
      (model.solve.dae.flat.context.site .equation) := by
    apply model.field_parent .derivativeFill
      (model.origins.extension.ref model.solve.origins.derivative.root)
      _ (model.solve.derivative_ancestry.extend model.origins.extension)
    simp [References.expected, Node.parents, _root_.Parser.Provenance.Table.Extension.ref]
  have observationTrace : TracesTo model.origins.table
      (model.origins.references.origin .observation)
      (model.solve.dae.flat.context.site .stateName) := by
    apply model.field_parent .observation
      (model.origins.extension.ref (model.solve.sourceOrigin .stateName)) _ (sourceTrace .stateName)
    simp [References.expected, Node.parents, _root_.Parser.Provenance.Table.Extension.ref]
  cases field with
  | model => exact modelTrace
  | input =>
    apply model.field_parent .input (model.origins.references.origin .model) _ modelTrace
    simp [References.expected, Node.parents]
  | observation => exact observationTrace
  | policy =>
    apply model.field_parent .policy (model.origins.extension.ref model.solve.origins.derivative.root)
      _ (model.solve.derivative_ancestry.extend model.origins.extension)
    simp [References.expected, Node.parents, _root_.Parser.Provenance.Table.Extension.ref]
  | time =>
    apply model.field_parent .time (model.origins.references.origin .model) _ modelTrace
    simp [References.expected, Node.parents]
  | derivativeName =>
    apply model.field_parent .derivativeName
      (model.origins.extension.ref (model.solve.sourceOrigin .stateName)) _ (sourceTrace .stateName)
    simp [References.expected, Node.parents, _root_.Parser.Provenance.Table.Extension.ref]
  | initialFill => exact initialTrace
  | initialReturn =>
    apply model.field_parent .initialReturn (model.origins.references.origin .initialFill) _ initialTrace
    simp [References.expected, Node.parents]
  | initialRead =>
    apply model.field_parent .initialRead (model.origins.references.origin .initialFill) _ initialTrace
    simp [References.expected, Node.parents]
  | derivativeFill => exact derivativeTrace
  | derivativeReturn =>
    apply model.field_parent .derivativeReturn
      (model.origins.references.origin .derivativeFill) _ derivativeTrace
    simp [References.expected, Node.parents]
  | derivativeRead =>
    apply model.field_parent .derivativeRead
      (model.origins.references.origin .derivativeFill) _ derivativeTrace
    simp [References.expected, Node.parents]
  | outputReturn =>
    apply model.field_parent .outputReturn
      (model.origins.references.origin .observation) _ observationTrace
    simp [References.expected, Node.parents]
  | outputRead =>
    apply model.field_parent .outputRead
      (model.origins.extension.ref (model.solve.sourceOrigin .stateName)) _ (sourceTrace .stateName)
    simp [References.expected, Node.parents, _root_.Parser.Provenance.Table.Extension.ref]

/-- A literal fill and its return/read occurrences must describe their actual
defining operation. Merely reaching some source leaf is insufficient. -/
def FMI3Origins.ConstantCorrect (table : Provenance.Table context)
    (expected : Node (_root_.Parser.Provenance.SourceRef context.input.inputs) Provenance.Rule) :
    Tensor.Program.Origins table (Tensor.fill (Γ := Γ) shape literal) → Prop
  | .fill operation (.ret returning reading) =>
      table.get operation = expected ∧
      table.get returning = .generated .tensorReturn operation.index.val #[] ∧
      table.get reading = .generated .tensorRead operation.index.val #[]

def FMI3Origins.ReadCorrect (table : Provenance.Table context)
    (operationNode readingNode :
      Node (_root_.Parser.Provenance.SourceRef context.input.inputs) Provenance.Rule) :
    Tensor.Program.Origins table (.ret register) → Prop
  | .ret operation reading => table.get operation = operationNode ∧ table.get reading = readingNode

/-- Independent requirements on the annotations of the actual IVP, including
metadata and every executable operation/operand. This does not call the origin
builder or its trace constructor to define correctness. -/
def FMI3Model.TraceCorrect (model : FMI3Model source) : Prop :=
  model.origins.table.get model.originTrace.model =
    .derived .prepareIVP model.solve.origins.derivative.root.index.val
      #[(model.solve.sourceOrigin .model).index.val] ∧
  model.origins.table.get model.originTrace.state =
    .source (model.solve.dae.flat.context.site .declaration) ∧
  model.origins.table.get model.originTrace.input =
    .generated .emptyInputChannel model.originTrace.model.index.val #[] ∧
  model.origins.table.get model.originTrace.output =
    .generated .stateObservation (model.solve.sourceOrigin .stateName).index.val
      #[(model.solve.sourceOrigin .declaration).index.val] ∧
  FMI3Origins.ConstantCorrect model.origins.table
    (.derived .tensorInitial model.solve.origins.completion.index.val #[])
    model.originTrace.initialProgram ∧
  FMI3Origins.ConstantCorrect model.origins.table
    (.derived .tensorDerivative model.solve.origins.derivative.root.index.val #[])
    model.originTrace.derivative ∧
  FMI3Origins.ReadCorrect model.origins.table
    (.generated .tensorReturn model.originTrace.output.index.val #[])
    (.generated .tensorRead (model.solve.sourceOrigin .stateName).index.val
      #[model.originTrace.output.index.val]) model.originTrace.observation

theorem FMI3Model.trace_correct (model : FMI3Model source) : model.TraceCorrect := by
  refine ⟨model.origins.correct.2 .model, model.source_origin .declaration,
    model.origins.correct.2 .input, model.origins.correct.2 .observation, ?_, ?_, ?_⟩
  · exact ⟨model.origins.correct.2 .initialFill, model.origins.correct.2 .initialReturn,
      model.origins.correct.2 .initialRead⟩
  · exact ⟨model.origins.correct.2 .derivativeFill, model.origins.correct.2 .derivativeReturn,
      model.origins.correct.2 .derivativeRead⟩
  · exact ⟨model.origins.correct.2 .outputReturn, model.origins.correct.2 .outputRead⟩

/-- The fixed tensor RHS is the interpretation of the stored scalar Solve
program, for every scalar arithmetic and literal interpretation. -/
theorem FMI3Model.rhs_matches_solve (model : FMI3Model source)
    (ops : Rumoca.Tensor.ScalarOps α) (zero one : α)
    (state : Rumoca.Tensor.Value α Rumoca.Tensor.scalar)
    (input : Rumoca.Tensor.Value α ⟨[0]⟩) :
    model.problem.rhs ops zero one state input =
      Rumoca.Tensor.Value.fill _ (evalWith one model.solve.derivative Fin.elim0) := by
  rw [model.solve.derivative_source]
  rfl

theorem FMI3Model.initial_matches_solve (model : FMI3Model source)
    (ops : Rumoca.Tensor.ScalarOps α) (interpret : Nat → α) :
    model.problem.initial ops (interpret 0) (interpret 1) =
      Rumoca.Tensor.Value.fill _ (interpret model.solve.initial.initial) := by
  rw [model.solve.initial_default]
  rfl

theorem FMI3Model.output_matches_state (model : FMI3Model source)
    (ops : Rumoca.Tensor.ScalarOps α) (zero one : α)
    (state : Rumoca.Tensor.Value α Rumoca.Tensor.scalar)
    (input : Rumoca.Tensor.Value α ⟨[0]⟩) :
    model.problem.outputs ops zero one state input = state := rfl

/-- One preparation guarantee binds the actual stored IVP, Solve model and
origin table. There is no successful-attachment or extra admission premise. -/
theorem FMI3Model.preparation_preserves (model : FMI3Model source)
    (ops : Rumoca.Tensor.ScalarOps α) (interpret : Nat → α)
    (state : Rumoca.Tensor.Value α Rumoca.Tensor.scalar)
    (input : Rumoca.Tensor.Value α ⟨[0]⟩) :
    model.problem.initial ops (interpret 0) (interpret 1) =
        Rumoca.Tensor.Value.fill _ (interpret model.solve.initial.initial) ∧
    model.problem.rhs ops (interpret 0) (interpret 1) state input =
        Rumoca.Tensor.Value.fill _ (evalWith (interpret 1) model.solve.derivative Fin.elim0) ∧
    model.problem.outputs ops (interpret 0) (interpret 1) state input = state ∧
    (∀ field, model.origins.table.get (model.origins.references.sourceOrigin field) =
      .source (model.solve.dae.flat.context.site field)) ∧
    (∀ field, TracesTo model.origins.table (model.origins.references.origin field)
      (model.solve.dae.flat.context.site field.sourceField)) ∧ model.TraceCorrect :=
  ⟨model.initial_matches_solve ops interpret,
    model.rhs_matches_solve ops (interpret 0) (interpret 1) state input,
    model.output_matches_state ops (interpret 0) (interpret 1) state input,
    model.source_origin, model.origin_ancestry, model.trace_correct⟩

end Rumoca.Solve
