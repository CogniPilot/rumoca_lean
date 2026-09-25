import RumocaCore.GALEC.UnitOrigins

/-! Independent provenance requirements on the actual prepared unit block.
Checking a role table alone does not establish that its references were attached
to the right operation, operand, method, target or declaration. -/
namespace Rumoca.GALEC
open _root_.Parser.Provenance (Ref Node)

/-- Every role, parent and rule of the unit block trace, and the operand and
returned-value occurrences that repeat an operation's origin. -/
def UnitOrigins.TraceCorrect (dae : DAE.Model source)
    {table : Provenance.Table dae.flat.context}
    (trace : Solve.Algorithm.Block.Origins table Solve.Algorithm.unitBlock) : Prop :=
  match trace.startup, trace.recalibrate, trace.doStep, trace.period with
  | .fill initial (.ret startupAssignment startupValue), .ret recalibrate recalibrateValue,
    .fill increment (.add addition stepRead stepOperand (.ret stepAssignment stepValue)),
    .fill period (.ret periodAssignment periodValue) =>
      table.get trace.model = .derived .algorithmAdmission dae.origins.expression.root.index.val
        #[dae.flat.origins.model.index.val] ∧
      table.get trace.stateDeclaration = .source (dae.flat.context.site .declaration) ∧
      table.get trace.periodDeclaration = .generated .unitSamplingPeriod trace.model.index.val #[] ∧
      table.get period = .generated .samplingPeriodValue trace.periodDeclaration.index.val #[] ∧
      (∃ fallback : Ref table,
        table.get fallback = .generated .realStartFallback dae.initializationOrigin.index.val #[] ∧
        table.get initial = .generated .selectUnfixedStart fallback.index.val #[]) ∧
      table.get trace.startupMethod = .generated .algorithmStartup trace.model.index.val
        #[initial.index.val, trace.periodDeclaration.index.val] ∧
      table.get startupAssignment = .generated .algorithmStateInitialization initial.index.val
        #[dae.flat.origins.state.index.val] ∧
      table.get trace.startupTarget = .generated .algorithmStateWrite startupAssignment.index.val
        #[dae.flat.origins.state.index.val] ∧
      table.get trace.recalibrateMethod = .generated .algorithmRecalibrate trace.model.index.val
        #[dae.flat.origins.declaration.index.val] ∧
      table.get trace.doStepMethod = .generated .algorithmDoStep trace.model.index.val
        #[dae.origins.expression.root.index.val, period.index.val] ∧
      table.get stepRead = .generated .algorithmStateRead trace.doStepMethod.index.val
        #[dae.flat.origins.state.index.val] ∧
      table.get increment = .derived .unitAlgorithmIncrement dae.origins.expression.root.index.val
        #[period.index.val] ∧
      table.get addition = .derived .unitAlgorithmStep dae.origins.expression.root.index.val
        #[stepRead.index.val, increment.index.val] ∧
      table.get stepAssignment = .generated .algorithmStateUpdate addition.index.val
        #[dae.flat.origins.state.index.val] ∧
      table.get trace.doStepTarget = .generated .algorithmStateWrite stepAssignment.index.val
        #[dae.flat.origins.state.index.val] ∧
      table.get periodAssignment = .generated .algorithmPeriodInitialization
        trace.startupMethod.index.val #[period.index.val] ∧
      table.get trace.periodTarget = .generated .algorithmPeriodWrite periodAssignment.index.val
        #[trace.periodDeclaration.index.val] ∧
      startupValue = initial ∧ recalibrate = trace.recalibrateMethod ∧
      recalibrateValue = trace.stateDeclaration ∧ trace.recalibrateTarget = trace.stateDeclaration ∧
      stepOperand = increment ∧ stepValue = addition ∧ periodValue = period

theorem UnitOrigins.References.trace_correct (dae : DAE.Model source)
    {table : Provenance.Table dae.flat.context} (refs : UnitOrigins.References table)
    (correct : refs.Correct dae)
    (declaration : table.get refs.stateDeclaration = .source (dae.flat.context.site .declaration)) :
    UnitOrigins.TraceCorrect dae refs.trace :=
  ⟨correct.2 .model, declaration, correct.2 .periodDeclaration, correct.2 .periodValue,
    ⟨refs.origin .fallback, correct.2 .fallback, correct.2 .initial⟩,
    correct.2 .startup, correct.2 .startupAssignment, correct.2 .startupTarget,
    correct.2 .recalibrate, correct.2 .doStep, correct.2 .stepRead, correct.2 .increment,
    correct.2 .addition, correct.2 .stepAssignment, correct.2 .stepTarget,
    correct.2 .periodAssignment, correct.2 .periodTarget,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Rumoca.GALEC
