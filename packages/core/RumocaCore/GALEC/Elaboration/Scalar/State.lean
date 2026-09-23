import RumocaCore.GALEC.Elaboration.Scalar.Execution
import RumocaCore.GALEC.UnitProfile

/-! Whole-shaped logical state across the two scalar method role layouts.
This transports values, not just declaration metadata. Source execution stays
relational and may use partial/nondeterministic arithmetic. No C connection,
source admission, or new method-permission policy is asserted. -/
namespace Rumoca.GALEC.Elaboration.Scalar.StateBridge
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor

def startupPack (b : Syntax.Block) (state : UnitProfile.State α) :
    Env α (Layout.outputShapes (startupFields b)) :=
  Env.push state.x (Env.push state.samplePeriod Env.empty)

def startupUnpack (b : Syntax.Block)
    (state : Env α (Layout.outputShapes (startupFields b))) : UnitProfile.State α :=
  ⟨state (startupState b), state (startupClock b)⟩

def stepInput (b : Syntax.Block) (state : UnitProfile.State α) :
    Env α (Layout.inputShapes (stepFields b)) :=
  Env.push state.samplePeriod Env.empty

def stepPack (b : Syntax.Block) (state : UnitProfile.State α) :
    Env α (Layout.outputShapes (stepFields b)) :=
  Env.push state.x Env.empty

def stepUnpack (b : Syntax.Block)
    (input : Env α (Layout.inputShapes (stepFields b)))
    (state : Env α (Layout.outputShapes (stepFields b))) : UnitProfile.State α :=
  ⟨state (stepState b), input .here⟩

theorem startup_roundtrip (b : Syntax.Block) (state : UnitProfile.State α) :
    startupUnpack b (startupPack b state) = state := rfl

theorem startup_repack (b : Syntax.Block)
    (state : Env α (Layout.outputShapes (startupFields b))) :
    @startupPack α b (startupUnpack b @state) = @state := by
  funext shape ref
  cases ref with
  | here => rfl
  | there ref =>
    cases ref with
    | here => rfl
    | there ref => cases ref

theorem step_roundtrip (b : Syntax.Block) (state : UnitProfile.State α) :
    stepUnpack b (stepInput b state) (stepPack b state) = state := rfl

theorem step_repack_input (b : Syntax.Block)
    (input : Env α (Layout.inputShapes (stepFields b)))
    (state : Env α (Layout.outputShapes (stepFields b))) :
    @stepInput α b (stepUnpack b @input @state) = @input := by
  funext shape ref
  cases ref with
  | here => rfl
  | there ref => cases ref

theorem step_repack_output (b : Syntax.Block)
    (input : Env α (Layout.inputShapes (stepFields b)))
    (state : Env α (Layout.outputShapes (stepFields b))) :
    @stepPack α b (stepUnpack b @input @state) = @state := by
  funext shape ref
  cases ref with
  | here => rfl
  | there ref => cases ref

theorem startup_unpack_injective (b : Syntax.Block) :
    Function.Injective (@startupUnpack α b) := by
  intro before after same
  have equal := congrArg (@startupPack α b) same
  simpa only [startup_repack] using equal

theorem step_unpack_injective (b : Syntax.Block)
    (input : Env α (Layout.inputShapes (stepFields b))) :
    Function.Injective (fun state => stepUnpack b @input @state) := by
  intro before after same
  have equal := congrArg (@stepPack α b) same
  simpa only [step_repack_output] using equal

theorem startup_updated_unpack (b : Syntax.Block) (zero one : α)
    (before : Env α (Layout.outputShapes (startupFields b))) :
    startupUnpack b (startupUpdated b zero one @before) =
      ⟨Value.fill scalar zero, Value.fill scalar one⟩ := rfl

theorem step_updated_unpack (b : Syntax.Block)
    (input : Env α (Layout.inputShapes (stepFields b)))
    (before : Env α (Layout.outputShapes (stepFields b))) (value : α) :
    stepUnpack b @input (Env.update before (stepState b) (Value.fill scalar value)) =
      ⟨Value.fill scalar value, (stepUnpack b @input @before).samplePeriod⟩ := rfl

/-- Independent logical method meaning. No AST lowerer, target statement,
source execution relation, or total evaluator occurs in this definition. -/
def Executes (step : BinaryOp → α → α → α → Prop) (zero one : α) :
    Method → UnitProfile.State α → UnitProfile.State α → Prop
  | .startup, _, after => after = ⟨Value.fill scalar zero, Value.fill scalar one⟩
  | .recalibrate, before, after => after = before
  | .doStep, before, after => ∃ value,
      step .add (before.x[Coordinate.index .nil]) one value ∧
        after = ⟨Value.fill scalar value, before.samplePeriod⟩

/-- Arbitrary actual Startup environments, not just an image chosen by pack. -/
theorem startup_source_iff (b : Syntax.Block) (resolved : Syntax.Resolved b) (ceiling : Nat)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes (startupFields b))) (env : IteratorEnv [])
    (before after : Env α (Layout.outputShapes (startupFields b))) :
    Bodies.Source.statements (Layout.bindings (startupFields b))
      (Declarations.ShapeLookup.HasShape ceiling (ProfileProjection.ofScalar b).declarations)
      ceiling step zero one @input .nil @env
      (ProfileProjection.startup b.initialState b.initialClock).body @before @after ↔
      Executes step zero one .startup (startupUnpack b @before) (startupUnpack b @after) := by
  rw [startup_source_executes b resolved ceiling]
  change (@after = @startupUpdated α b zero one @before) ↔
    startupUnpack b @after = ⟨Value.fill scalar zero, Value.fill scalar one⟩
  rw [← startup_updated_unpack b zero one @before]
  exact ⟨congrArg (@startupUnpack α b), fun same => startup_unpack_injective b same⟩

/-- The immutable input contributes the very same period before and after. -/
theorem recalibrate_source_iff (b : Syntax.Block) (resolved : Syntax.Resolved b) (ceiling : Nat)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes (stepFields b))) (env : IteratorEnv [])
    (before after : Env α (Layout.outputShapes (stepFields b))) :
    Bodies.Source.statements (Layout.bindings (stepFields b))
      (Declarations.ShapeLookup.HasShape ceiling (ProfileProjection.ofScalar b).declarations)
      ceiling step zero one @input .nil @env ProfileProjection.recalibrate.body @before @after ↔
      Executes step zero one .recalibrate
        (stepUnpack b @input @before) (stepUnpack b @input @after) := by
  rw [recalibrate_source_executes b resolved ceiling]
  change (@after = @before) ↔ stepUnpack b @input @after = stepUnpack b @input @before
  exact ⟨congrArg (fun state => stepUnpack b @input @state),
    fun same => step_unpack_injective b @input same⟩

/-- Exact partial addition domain and result, with whole-shaped clock frame. -/
theorem step_source_iff (b : Syntax.Block) (resolved : Syntax.Resolved b) (ceiling : Nat)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes (stepFields b))) (env : IteratorEnv [])
    (before after : Env α (Layout.outputShapes (stepFields b))) :
    Bodies.Source.statements (Layout.bindings (stepFields b))
      (Declarations.ShapeLookup.HasShape ceiling (ProfileProjection.ofScalar b).declarations)
      ceiling step zero one @input .nil @env
      (ProfileProjection.scalarStep b.stepTarget b.stepRead).body @before @after ↔
      Executes step zero one .doStep
        (stepUnpack b @input @before) (stepUnpack b @input @after) := by
  rw [step_source_executes b resolved ceiling]
  unfold Executes
  apply exists_congr
  intro value
  apply and_congr_right
  intro _
  rw [← step_updated_unpack b @input @before value]
  exact ⟨congrArg (fun state => stepUnpack b @input @state),
    fun same => step_unpack_injective b @input same⟩

/-- Total unitBlock correspondence needs only the arithmetic actually used:
addition of the distinguished one. Nothing assumes other operations total. -/
theorem executes_iff_unitBlock (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (add : α → α → α)
    (arithmetic : ∀ x result, step .add x one result ↔ result = add x one)
    (method : Method) (before after : UnitProfile.State α) :
    Executes step zero one method before after ↔
      after = UnitProfile.execute unitBlock zero one add method before := by
  cases method with
  | startup => rfl
  | recalibrate => rfl
  | doStep =>
    simp only [Executes, arithmetic, exists_eq_left]
    have valueEq : zipWith add before.x (Value.fill scalar one) =
        Value.fill scalar (add (before.x[Coordinate.index .nil]) one) := by
      apply Value.ext
      intro i hi
      have atZero : i = 0 := by change i < 1 at hi; omega
      subst i
      simp only [get_zipWith, Value.getElem_fill]
      rfl
    simp only [UnitProfile.execute, Block.execute, unitBlock, Block.body, Expr.eval, valueEq]

/-- The original embedded method, with every source spelling retained. -/
def originalMethod (b : Syntax.Block) : Method → AST.Method
  | .startup => ProfileProjection.startup b.initialState b.initialClock
  | .recalibrate => ProfileProjection.recalibrate
  | .doStep => ProfileProjection.scalarStep b.stepTarget b.stepRead

theorem selected_original (b : Syntax.Block) (method : Method) :
    Methods.Headers.Selects (originalMethod b method).name
      (ProfileProjection.ofScalar b).methods (originalMethod b method) := by
  cases method with
  | startup => exact startup_selected b
  | recalibrate => exact recalibrate_selected b
  | doStep => exact step_selected b

/-- Original source execution viewed in the shared logical state. Pack the
entire pre-state into the method's roles; execute its actual body; unpack its
actual post-store. In non-Startup methods, unpack reuses the SAME immutable
period input, so an arbitrary different post-period cannot be hidden. -/
def SourceExec (b : Syntax.Block) (ceiling : Nat)
    (step : BinaryOp → α → α → α → Prop) (zero one : α) :
    Method → UnitProfile.State α → UnitProfile.State α → Prop
  | .startup, before, after => ∃ next : Env α (Layout.outputShapes (startupFields b)),
      Bodies.Source.statements (Layout.bindings (startupFields b))
        (Declarations.ShapeLookup.HasShape ceiling (ProfileProjection.ofScalar b).declarations)
        ceiling step zero one Env.empty .nil IteratorEnv.empty
        (originalMethod b .startup).body (startupPack b before) @next ∧
          after = startupUnpack b @next
  | method, before, after => ∃ next : Env α (Layout.outputShapes (stepFields b)),
      Bodies.Source.statements (Layout.bindings (stepFields b))
        (Declarations.ShapeLookup.HasShape ceiling (ProfileProjection.ofScalar b).declarations)
        ceiling step zero one (stepInput b before) .nil IteratorEnv.empty
        (originalMethod b method).body (stepPack b before) @next ∧
          after = stepUnpack b (stepInput b before) @next

/-- All original resolved names, all ceilings (including zero), all states,
and arbitrary partial/nondeterministic arithmetic; no target semantics in the
independent logical relation and no replacement source body in the wrapper. -/
theorem source_iff (b : Syntax.Block) (resolved : Syntax.Resolved b) (ceiling : Nat)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (method : Method) (before after : UnitProfile.State α) :
    SourceExec b ceiling step zero one method before after ↔
      Executes step zero one method before after := by
  cases method with
  | startup =>
    simp only [SourceExec, originalMethod, startup_source_iff b resolved ceiling,
      startup_roundtrip]
    constructor
    · rintro ⟨next, executed, rfl⟩
      exact executed
    · intro executed
      exact ⟨startupPack b after, by simpa only [startup_roundtrip] using executed,
        (startup_roundtrip b after).symm⟩
  | recalibrate =>
    simp only [SourceExec, originalMethod, recalibrate_source_iff b resolved ceiling,
      step_roundtrip]
    constructor
    · rintro ⟨next, executed, rfl⟩
      exact executed
    · intro executed
      change after = before at executed
      subst after
      exact ⟨stepPack b before, by rw [step_roundtrip]; rfl,
        (step_roundtrip b before).symm⟩
  | doStep =>
    simp only [SourceExec, originalMethod, step_source_iff b resolved ceiling,
      step_roundtrip]
    constructor
    · rintro ⟨next, executed, rfl⟩
      exact executed
    · rintro ⟨value, arithmetic, rfl⟩
      exact ⟨stepPack b ⟨Value.fill scalar value, before.samplePeriod⟩,
        ⟨value, arithmetic, rfl⟩, rfl⟩

theorem sourceExec_iff_unitBlock (b : Syntax.Block) (resolved : Syntax.Resolved b) (ceiling : Nat)
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (add : α → α → α)
    (arithmetic : ∀ x result, step .add x one result ↔ result = add x one)
    (method : Method) (before after : UnitProfile.State α) :
    SourceExec b ceiling step zero one method before after ↔
      after = UnitProfile.execute unitBlock zero one add method before :=
  (source_iff b resolved ceiling step zero one method before after).trans
    (executes_iff_unitBlock step zero one add arithmetic method before after)

end Rumoca.GALEC.Elaboration.Scalar.StateBridge
