import RumocaCore.GALEC.Elaboration.Scalar.Preparation
import RumocaCore.GALEC.InitializationBodies
import RumocaCore.GALEC.StatementRelations

/-! Original scalar bodies and exact store effects through the generic lowerer.
Arithmetic remains partial/nondeterministic; DoStep does not assume addition
succeeds. The immutable clock environment is separate from writable state. -/
namespace Rumoca.GALEC.Elaboration.Scalar
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor

/-- A reusable rank-zero assignment law, with an arbitrary expression. -/
theorem scalar_assign_iff (ref : Ref outputs scalar) (term : ScalarTerm inputs outputs bounds)
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs)
    (env : IteratorEnv bounds) (before after : Env α outputs) :
    (Statement.assign ref .nil term).Executes step zero one @input @env @before @after ↔
      ∃ value, term.Evaluates step zero one @input @before @env value ∧
        @after = @Env.update α outputs scalar @before ref (Value.fill scalar value) := by
  simp only [Statement.Executes, Subscripts.eval, InitializationBodies.scalar_write_iff,
    Env.update_correct]
  constructor
  · rintro ⟨value, tensor, evaluated, rfl, same⟩
    exact ⟨value, evaluated, same⟩
  · rintro ⟨value, evaluated, same⟩
    exact ⟨value, _, evaluated, rfl, same⟩

theorem scalar_literal_iff (ref : Ref outputs scalar) (literal : Literal)
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs)
    (env : IteratorEnv bounds) (before after : Env α outputs) :
    (Statement.assign ref .nil (.literal literal)).Executes step zero one @input @env @before @after ↔
      @after = @Env.update α outputs scalar @before ref (Value.fill scalar (literal.eval zero one)) := by
  rw [scalar_assign_iff]
  constructor
  · rintro ⟨value, evaluated, same⟩
    cases evaluated
    exact same
  · intro same
    exact ⟨_, .literal literal, same⟩

def startupUpdated (state clock : String) (zero one : α)
    (before : Env α (Layout.outputShapes (startupFields state clock))) :
    Env α (Layout.outputShapes (startupFields state clock)) :=
  Env.update (Env.update before (startupState state clock) (Value.fill scalar zero))
    (startupClock state clock) (Value.fill scalar one)

theorem startup_executes (state clock : String)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes (startupFields state clock))) (env : IteratorEnv [])
    (before after : Env α (Layout.outputShapes (startupFields state clock))) :
    (startupResult state clock).2.Executes step zero one @input @env @before @after ↔
      @after = @startupUpdated α state clock zero one @before := by
  change (∃ middle, (Statement.assign (startupState state clock) .nil (.literal .zero)).Executes
    step zero one @input @env @before @middle ∧ ∃ next,
    (Statement.assign (startupClock state clock) .nil (.literal .one)).Executes
      step zero one @input @env @middle @next ∧ @after = @next) ↔ _
  simp only [scalar_literal_iff, Literal.eval, exists_eq_left]
  rfl

theorem recalibrate_executes (state clock : String)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes (stepFields state clock))) (env : IteratorEnv [])
    (before after : Env α (Layout.outputShapes (stepFields state clock))) :
    (recalibrateResult state clock).2.Executes step zero one @input @env @before @after ↔
      @after = @before := Iff.rfl

theorem increment_evaluates (ref : Ref outputs scalar)
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs)
    (env : IteratorEnv bounds) (before : Env α outputs) (value : α) :
    (ScalarTerm.binary .add (.output ref .nil) (.literal .one)).Evaluates
      step zero one @input @before @env value ↔
      step .add ((before ref)[Coordinate.index .nil]) one value := by
  constructor
  · intro evaluated
    cases evaluated with
    | binary left right arithmetic =>
      cases left
      cases right
      exact arithmetic
  · intro arithmetic
    exact .binary (.output ref .nil) (.literal .one) arithmetic

theorem step_executes (state clock : String)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes (stepFields state clock))) (env : IteratorEnv [])
    (before after : Env α (Layout.outputShapes (stepFields state clock))) :
    (stepResult state clock).2.Executes step zero one @input @env @before @after ↔
      ∃ value, step .add ((before (stepState state clock))[Coordinate.index .nil]) one value ∧
        @after = @Env.update α _ scalar @before (stepState state clock) (Value.fill scalar value) := by
  exact (StatementRelations.seq_skip_right step zero one @input _ @env @before @after).trans
    ((scalar_assign_iff _ _ step zero one @input @env @before @after).trans
      (by simp only [increment_evaluates]))

theorem startup_source_executes (different : state ≠ clock) (ceiling : Nat)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes (startupFields state clock))) (env : IteratorEnv [])
    (before after : Env α (Layout.outputShapes (startupFields state clock))) :
    Bodies.Source.statements (Layout.bindings (startupFields state clock))
      (Declarations.ShapeLookup.HasShape ceiling (sourceDeclarations state clock))
      ceiling step zero one @input .nil @env
      (startupMethod state clock).body @before @after ↔
      @after = @startupUpdated α state clock zero one @before := by
  have fieldsDeclared := Methods.Preparation.declared_fields Capabilities.Initialization.role
    (declared different ceiling)
  have lowered := (Layout.body_iff _ fieldsDeclared _ _).mpr (startup_typed different ceiling)
  exact (Layout.source_to_body _ fieldsDeclared _ _ lowered step zero one @input @env @before @after).trans
    (startup_executes state clock step zero one @input @env @before @after)

theorem recalibrate_source_executes (different : state ≠ clock) (ceiling : Nat)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes (stepFields state clock))) (env : IteratorEnv [])
    (before after : Env α (Layout.outputShapes (stepFields state clock))) :
    Bodies.Source.statements (Layout.bindings (stepFields state clock))
      (Declarations.ShapeLookup.HasShape ceiling (sourceDeclarations state clock))
      ceiling step zero one @input .nil @env recalibrateMethod.body @before @after ↔
      @after = @before := by
  have fieldsDeclared := Methods.Preparation.declared_fields Capabilities.DoStep.role
    (declared different ceiling)
  have lowered := (Layout.body_iff _ fieldsDeclared _ .skip).mpr
    (Bodies.BodyElaborates.nil (table := Layout.bindings (stepFields state clock))
      (HasShape := Declarations.ShapeLookup.HasShape ceiling (sourceDeclarations state clock))
      (ceiling := ceiling) (names := .nil))
  exact Layout.source_to_body _ fieldsDeclared _ .skip lowered step zero one @input @env @before @after

theorem step_source_executes (different : state ≠ clock) (ceiling : Nat)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes (stepFields state clock))) (env : IteratorEnv [])
    (before after : Env α (Layout.outputShapes (stepFields state clock))) :
    Bodies.Source.statements (Layout.bindings (stepFields state clock))
      (Declarations.ShapeLookup.HasShape ceiling (sourceDeclarations state clock))
      ceiling step zero one @input .nil @env
      (stepMethod state).body @before @after ↔
      ∃ value, step .add ((before (stepState state clock))[Coordinate.index .nil]) one value ∧
        @after = @Env.update α _ scalar @before (stepState state clock) (Value.fill scalar value) := by
  have fieldsDeclared := Methods.Preparation.declared_fields Capabilities.DoStep.role
    (declared different ceiling)
  have lowered := (Layout.body_iff _ fieldsDeclared _ _).mpr (step_typed state clock ceiling)
  exact (Layout.source_to_body _ fieldsDeclared _ _ lowered step zero one @input @env @before @after).trans
    (step_executes state clock step zero one @input @env @before @after)

end Rumoca.GALEC.Elaboration.Scalar
