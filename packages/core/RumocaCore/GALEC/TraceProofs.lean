import RumocaCore.GALEC.OriginProofs

/-! Independent provenance requirements on the actual Algorithm Code block.
Checking a role table alone does not establish that its references were attached
to the right expression, assignment, method or declaration. -/
namespace Rumoca.GALEC
open _root_.Parser.Provenance (Ref Node)

def UnitOrigins.TraceCorrect (dae : DAE.Model source)
    {table : Provenance.Table dae.flat.context} (trace : Block.Origins table unitBlock) : Prop :=
  match trace.startup, trace.recalibrate, trace.doStep, trace.periodValue with
  | .assign startup startupAssignment startupTarget (.zero initial), .empty recalibrate,
    .assign doStep stepAssignment stepTarget (.add addition (.state stepRead) (.one increment)),
    .one period =>
      table.get trace.model = .derived .algorithmAdmission dae.origins.expression.root.index.val
        #[dae.flat.origins.model.index.val] ∧
      table.get trace.stateDeclaration = .source (dae.flat.context.site .declaration) ∧
      table.get trace.periodDeclaration = .generated .unitSamplingPeriod trace.model.index.val #[] ∧
      table.get period = .generated .samplingPeriodValue trace.periodDeclaration.index.val #[] ∧
      (∃ fallback : Ref table,
        table.get fallback = .generated .realStartFallback dae.initializationOrigin.index.val #[] ∧
        table.get initial = .generated .selectUnfixedStart fallback.index.val #[]) ∧
      table.get startup = .generated .algorithmStartup trace.model.index.val
        #[initial.index.val, trace.periodDeclaration.index.val] ∧
      table.get startupAssignment = .generated .algorithmStateInitialization initial.index.val
        #[dae.flat.origins.state.index.val] ∧
      table.get startupTarget = .generated .algorithmStateWrite startupAssignment.index.val
        #[dae.flat.origins.state.index.val] ∧
      table.get recalibrate = .generated .algorithmRecalibrate trace.model.index.val
        #[dae.flat.origins.declaration.index.val] ∧
      table.get doStep = .generated .algorithmDoStep trace.model.index.val
        #[dae.origins.expression.root.index.val, period.index.val] ∧
      table.get stepRead = .generated .algorithmStateRead doStep.index.val
        #[dae.flat.origins.state.index.val] ∧
      table.get increment = .derived .unitAlgorithmIncrement dae.origins.expression.root.index.val
        #[period.index.val] ∧
      table.get addition = .derived .unitAlgorithmStep dae.origins.expression.root.index.val
        #[stepRead.index.val, increment.index.val] ∧
      table.get stepAssignment = .generated .algorithmStateUpdate addition.index.val
        #[dae.flat.origins.state.index.val] ∧
      table.get stepTarget = .generated .algorithmStateWrite stepAssignment.index.val
        #[dae.flat.origins.state.index.val] ∧
      table.get trace.periodAssignment = .generated .algorithmPeriodInitialization startup.index.val
        #[period.index.val] ∧
      table.get trace.periodTarget = .generated .algorithmPeriodWrite trace.periodAssignment.index.val
        #[trace.periodDeclaration.index.val]

theorem UnitOrigins.References.trace_correct (dae : DAE.Model source)
    {table : Provenance.Table dae.flat.context} (refs : UnitOrigins.References table)
    (correct : refs.Correct dae)
    (declaration : table.get refs.stateDeclaration = .source (dae.flat.context.site .declaration)) :
    UnitOrigins.TraceCorrect dae refs.trace := by
  exact ⟨correct.2 .model, declaration, correct.2 .periodDeclaration, correct.2 .periodValue,
    ⟨refs.origin .fallback, correct.2 .fallback, correct.2 .initial⟩,
    correct.2 .startup, correct.2 .startupAssignment, correct.2 .startupTarget,
    correct.2 .recalibrate, correct.2 .doStep, correct.2 .stepRead, correct.2 .increment,
    correct.2 .addition, correct.2 .stepAssignment, correct.2 .stepTarget,
    correct.2 .periodAssignment, correct.2 .periodTarget⟩

/-- The profile equality changes only the index of this actual block trace. -/
def Model.TraceCorrect (model : Model source) : Prop :=
  UnitOrigins.TraceCorrect model.dae (model.profile ▸ model.originTrace)

theorem Model.trace_correct (model : Model source) : model.TraceCorrect := by
  rcases model with ⟨dae, block, profile, origins⟩
  cases profile
  exact origins.references.trace_correct dae origins.correct
    (Model.state_origin ⟨dae, unitBlock, rfl, origins⟩)

end Rumoca.GALEC
