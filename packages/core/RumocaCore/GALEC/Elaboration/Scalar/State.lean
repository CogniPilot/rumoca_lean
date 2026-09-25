import RumocaCore.GALEC.Elaboration.Scalar.Execution
import RumocaCore.GALEC.UnitProfile

/-! Whole-shaped logical state across the two scalar method role layouts.
This transports values, not just declaration metadata. Source execution stays
relational and may use partial/nondeterministic arithmetic. No C connection,
source admission, or new method-permission policy is asserted. -/
namespace Rumoca.GALEC.Elaboration.Scalar.StateBridge
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor

def startupPack (stateName clockName : String) (state : UnitProfile.State α) :
    Env α (Layout.outputShapes (startupFields stateName clockName)) :=
  Env.push state.x (Env.push state.samplePeriod Env.empty)

def startupUnpack (stateName clockName : String)
    (state : Env α (Layout.outputShapes (startupFields stateName clockName))) : UnitProfile.State α :=
  ⟨state (startupState stateName clockName), state (startupClock stateName clockName)⟩

def stepInput (stateName clockName : String) (state : UnitProfile.State α) :
    Env α (Layout.inputShapes (stepFields stateName clockName)) :=
  Env.push state.samplePeriod Env.empty

def stepPack (stateName clockName : String) (state : UnitProfile.State α) :
    Env α (Layout.outputShapes (stepFields stateName clockName)) :=
  Env.push state.x Env.empty

def stepUnpack (stateName clockName : String)
    (input : Env α (Layout.inputShapes (stepFields stateName clockName)))
    (state : Env α (Layout.outputShapes (stepFields stateName clockName))) : UnitProfile.State α :=
  ⟨state (stepState stateName clockName), input .here⟩

theorem startup_roundtrip (stateName clockName : String) (state : UnitProfile.State α) :
    startupUnpack stateName clockName (startupPack stateName clockName state) = state := rfl

theorem startup_repack (stateName clockName : String)
    (state : Env α (Layout.outputShapes (startupFields stateName clockName))) :
    @startupPack α stateName clockName (startupUnpack stateName clockName @state) = @state := by
  funext shape ref
  cases ref with
  | here => rfl
  | there ref =>
    cases ref with
    | here => rfl
    | there ref => cases ref

theorem step_roundtrip (stateName clockName : String) (state : UnitProfile.State α) :
    stepUnpack stateName clockName (stepInput stateName clockName state) (stepPack stateName clockName state) = state := rfl

theorem step_repack_input (stateName clockName : String)
    (input : Env α (Layout.inputShapes (stepFields stateName clockName)))
    (state : Env α (Layout.outputShapes (stepFields stateName clockName))) :
    @stepInput α stateName clockName (stepUnpack stateName clockName @input @state) = @input := by
  funext shape ref
  cases ref with
  | here => rfl
  | there ref => cases ref

theorem step_repack_output (stateName clockName : String)
    (input : Env α (Layout.inputShapes (stepFields stateName clockName)))
    (state : Env α (Layout.outputShapes (stepFields stateName clockName))) :
    @stepPack α stateName clockName (stepUnpack stateName clockName @input @state) = @state := by
  funext shape ref
  cases ref with
  | here => rfl
  | there ref => cases ref

theorem startup_unpack_injective (stateName clockName : String) :
    Function.Injective (@startupUnpack α stateName clockName) := by
  intro before after same
  have equal := congrArg (@startupPack α stateName clockName) same
  simpa only [startup_repack] using equal

theorem step_unpack_injective (stateName clockName : String)
    (input : Env α (Layout.inputShapes (stepFields stateName clockName))) :
    Function.Injective (fun state => stepUnpack stateName clockName @input @state) := by
  intro before after same
  have equal := congrArg (@stepPack α stateName clockName) same
  simpa only [step_repack_output] using equal

theorem startup_updated_unpack (stateName clockName : String) (zero one : α)
    (before : Env α (Layout.outputShapes (startupFields stateName clockName))) :
    startupUnpack stateName clockName (startupUpdated stateName clockName zero one @before) =
      ⟨Value.fill scalar zero, Value.fill scalar one⟩ := rfl

theorem step_updated_unpack (stateName clockName : String)
    (input : Env α (Layout.inputShapes (stepFields stateName clockName)))
    (before : Env α (Layout.outputShapes (stepFields stateName clockName))) (value : α) :
    stepUnpack stateName clockName @input (Env.update before (stepState stateName clockName) (Value.fill scalar value)) =
      ⟨Value.fill scalar value, (stepUnpack stateName clockName @input @before).samplePeriod⟩ := rfl

/-- Independent logical method meaning. No AST lowerer, target statement,
source execution relation, or total evaluator occurs in this definition. -/
def Executes (step : BinaryOp → α → α → α → Prop) (zero one : α) :
    Method → UnitProfile.State α → UnitProfile.State α → Prop
  | .startup, _, after => after = ⟨Value.fill scalar zero, Value.fill scalar one⟩
  | .recalibrate, before, after => after = before
  | .doStep, before, after => ∃ value,
      step .add (before.x[Coordinate.index .nil]) one value ∧
        after = ⟨Value.fill scalar value, before.samplePeriod⟩

/-- Arbitrary actual Startup environments, not just an image chosen by pack,
for the selected Startup method of any block that prepares to the scalar
Startup result. -/
theorem startup_source_iff
    (prepared : Methods.Preparation.Prepares (.ident "Startup") Capabilities.Initialization.role
      ceiling block (startupResult stateName clockName))
    (selected : Methods.Headers.Selects (.ident "Startup") block.methods method)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes (startupFields stateName clockName))) (env : IteratorEnv [])
    (before after : Env α (Layout.outputShapes (startupFields stateName clockName))) :
    Bodies.Source.statements (Layout.bindings (startupFields stateName clockName))
      (Declarations.ShapeLookup.HasShape ceiling block.declarations)
      ceiling step zero one @input .nil @env method.body @before @after ↔
      Executes step zero one .startup (startupUnpack stateName clockName @before) (startupUnpack stateName clockName @after) := by
  refine (Methods.Correspondence.selected_execution prepared selected step zero one
    @input @env @before @after).trans ((startup_executes stateName clockName step zero one
      @input @env @before @after).trans ?_)
  change (@after = @startupUpdated α stateName clockName zero one @before) ↔
    startupUnpack stateName clockName @after = ⟨Value.fill scalar zero, Value.fill scalar one⟩
  rw [← startup_updated_unpack stateName clockName zero one @before]
  exact ⟨congrArg (@startupUnpack α stateName clockName), fun same => startup_unpack_injective stateName clockName same⟩

/-- The immutable input contributes the very same period before and after. -/
theorem recalibrate_source_iff
    (prepared : Methods.Preparation.Prepares (.ident "Recalibrate") Capabilities.DoStep.role
      ceiling block (recalibrateResult stateName clockName))
    (selected : Methods.Headers.Selects (.ident "Recalibrate") block.methods method)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes (stepFields stateName clockName))) (env : IteratorEnv [])
    (before after : Env α (Layout.outputShapes (stepFields stateName clockName))) :
    Bodies.Source.statements (Layout.bindings (stepFields stateName clockName))
      (Declarations.ShapeLookup.HasShape ceiling block.declarations)
      ceiling step zero one @input .nil @env method.body @before @after ↔
      Executes step zero one .recalibrate
        (stepUnpack stateName clockName @input @before) (stepUnpack stateName clockName @input @after) := by
  refine (Methods.Correspondence.selected_execution prepared selected step zero one
    @input @env @before @after).trans ((recalibrate_executes stateName clockName step zero one
      @input @env @before @after).trans ?_)
  change (@after = @before) ↔ stepUnpack stateName clockName @input @after = stepUnpack stateName clockName @input @before
  exact ⟨congrArg (fun state => stepUnpack stateName clockName @input @state),
    fun same => step_unpack_injective stateName clockName @input same⟩

/-- Exact partial addition domain and result, with whole-shaped clock frame. -/
theorem step_source_iff
    (prepared : Methods.Preparation.Prepares (.ident "DoStep") Capabilities.DoStep.role
      ceiling block (stepResult stateName clockName))
    (selected : Methods.Headers.Selects (.ident "DoStep") block.methods method)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes (stepFields stateName clockName))) (env : IteratorEnv [])
    (before after : Env α (Layout.outputShapes (stepFields stateName clockName))) :
    Bodies.Source.statements (Layout.bindings (stepFields stateName clockName))
      (Declarations.ShapeLookup.HasShape ceiling block.declarations)
      ceiling step zero one @input .nil @env method.body @before @after ↔
      Executes step zero one .doStep
        (stepUnpack stateName clockName @input @before) (stepUnpack stateName clockName @input @after) := by
  refine (Methods.Correspondence.selected_execution prepared selected step zero one
    @input @env @before @after).trans ((step_executes stateName clockName step zero one
      @input @env @before @after).trans ?_)
  unfold Executes
  apply exists_congr
  intro value
  apply and_congr_right
  intro _
  rw [← step_updated_unpack stateName clockName @input @before value]
  exact ⟨congrArg (fun state => stepUnpack stateName clockName @input @state),
    fun same => step_unpack_injective stateName clockName @input same⟩

/-- Total correspondence with the prepared unit block needs only the arithmetic
actually used: addition of the distinguished one. Nothing assumes other
operations total. -/
theorem executes_iff_solve (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (add : α → α → α)
    (arithmetic : ∀ x result, step .add x one result ↔ result = add x one)
    (method : Method) (before after : UnitProfile.State α) :
    Executes step zero one method before after ↔
      after = UnitProfile.solveExecute Solve.Algorithm.unitBlock zero one add method before := by
  cases method with
  | startup => rfl
  | recalibrate => rfl
  | doStep =>
    simp only [Executes, arithmetic, exists_eq_left]
    have valueEq : before.x.zipWith add (Value.fill scalar one) =
        Value.fill scalar (add (before.x[Coordinate.index .nil]) one) := by
      apply Value.ext
      intro i hi
      have atZero : i = 0 := by change i < 1 at hi; omega
      subst i
      simp only [Value.getElem_zipWith, Value.getElem_fill]
      rfl
    simp only [UnitProfile.solveExecute, Solve.Algorithm.Block.execute, Solve.Algorithm.unitBlock,
      Solve.Algorithm.Block.body, Solve.Algorithm.Program.eval, Solve.Tensor.Literal.eval]
    exact iff_of_eq (congrArg (after = ·) (congrArg (UnitProfile.State.mk · before.samplePeriod)
      valueEq.symm))

/-- Original source execution of the method selected by name in `block`,
viewed in the shared logical state. Pack the entire pre-state into the
method's roles; execute its actual body; unpack its actual post-store. In
non-Startup methods, unpack reuses the SAME immutable period input, so an
arbitrary different post-period cannot be hidden. -/
def SourceExec (block : AST.Block) (stateName clockName : String) (ceiling : Nat)
    (step : BinaryOp → α → α → α → Prop) (zero one : α) :
    Method → UnitProfile.State α → UnitProfile.State α → Prop
  | .startup, before, after => ∃ (method : AST.Method)
      (next : Env α (Layout.outputShapes (startupFields stateName clockName))),
      Methods.Headers.Selects (.ident "Startup") block.methods method ∧
      Bodies.Source.statements (Layout.bindings (startupFields stateName clockName))
        (Declarations.ShapeLookup.HasShape ceiling block.declarations)
        ceiling step zero one Env.empty .nil IteratorEnv.empty
        method.body (startupPack stateName clockName before) @next ∧
          after = startupUnpack stateName clockName @next
  | .recalibrate, before, after => ∃ (method : AST.Method)
      (next : Env α (Layout.outputShapes (stepFields stateName clockName))),
      Methods.Headers.Selects (.ident "Recalibrate") block.methods method ∧
      Bodies.Source.statements (Layout.bindings (stepFields stateName clockName))
        (Declarations.ShapeLookup.HasShape ceiling block.declarations)
        ceiling step zero one (stepInput stateName clockName before) .nil IteratorEnv.empty
        method.body (stepPack stateName clockName before) @next ∧
          after = stepUnpack stateName clockName (stepInput stateName clockName before) @next
  | .doStep, before, after => ∃ (method : AST.Method)
      (next : Env α (Layout.outputShapes (stepFields stateName clockName))),
      Methods.Headers.Selects (.ident "DoStep") block.methods method ∧
      Bodies.Source.statements (Layout.bindings (stepFields stateName clockName))
        (Declarations.ShapeLookup.HasShape ceiling block.declarations)
        ceiling step zero one (stepInput stateName clockName before) .nil IteratorEnv.empty
        method.body (stepPack stateName clockName before) @next ∧
          after = stepUnpack stateName clockName (stepInput stateName clockName before) @next

/-- For every block that prepares to the scalar method results, under any
header interface: all ceilings (including zero), all states, and arbitrary
partial/nondeterministic arithmetic; no target semantics in the independent
logical relation and no replacement source body in the wrapper. -/
theorem source_iff
    (prepared : Block.Prepares ceiling block (preparedResult stateName clockName selection))
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (method : Method) (before after : UnitProfile.State α) :
    SourceExec block stateName clockName ceiling step zero one method before after ↔
      Executes step zero one method before after := by
  cases method with
  | startup =>
    constructor
    · rintro ⟨selectedMethod, next, selected, executed, rfl⟩
      have := (startup_source_iff prepared.startup selected step zero one Env.empty IteratorEnv.empty
        _ @next).mp executed
      rwa [startup_roundtrip] at this
    · intro executed
      refine ⟨_, startupPack stateName clockName after, prepared.headers.startup,
        (startup_source_iff prepared.startup prepared.headers.startup step zero one Env.empty
          IteratorEnv.empty _ _).mpr ?_, (startup_roundtrip stateName clockName after).symm⟩
      simpa only [startup_roundtrip] using executed
  | recalibrate =>
    constructor
    · rintro ⟨selectedMethod, next, selected, executed, rfl⟩
      have := (recalibrate_source_iff prepared.recalibrate selected step zero one _ IteratorEnv.empty
        _ @next).mp executed
      rwa [step_roundtrip] at this
    · intro executed
      change after = before at executed
      subst after
      refine ⟨_, stepPack stateName clockName before, prepared.headers.recalibrate,
        (recalibrate_source_iff prepared.recalibrate prepared.headers.recalibrate step zero one _
          IteratorEnv.empty _ _).mpr ?_, (step_roundtrip stateName clockName before).symm⟩
      rw [step_roundtrip]
      rfl
  | doStep =>
    constructor
    · rintro ⟨selectedMethod, next, selected, executed, rfl⟩
      have := (step_source_iff prepared.doStep selected step zero one _ IteratorEnv.empty
        _ @next).mp executed
      rwa [step_roundtrip] at this
    · rintro ⟨value, arithmetic, rfl⟩
      exact ⟨_, stepPack stateName clockName ⟨Value.fill scalar value, before.samplePeriod⟩,
        prepared.headers.doStep,
        (step_source_iff prepared.doStep prepared.headers.doStep step zero one _ IteratorEnv.empty
          _ _).mpr (by rw [step_roundtrip]; exact ⟨value, arithmetic, rfl⟩), rfl⟩

/-- GALEC to Solve: original source execution of a block that prepares to the
scalar results is exactly the prepared unit Solve block's execution. -/
theorem sourceExec_iff_solve
    (prepared : Block.Prepares ceiling block (preparedResult stateName clockName selection))
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (add : α → α → α)
    (arithmetic : ∀ x result, step .add x one result ↔ result = add x one)
    (method : Method) (before after : UnitProfile.State α) :
    SourceExec block stateName clockName ceiling step zero one method before after ↔
      after = UnitProfile.solveExecute Solve.Algorithm.unitBlock zero one add method before :=
  (source_iff prepared step zero one method before after).trans
    (executes_iff_solve step zero one add arithmetic method before after)

end Rumoca.GALEC.Elaboration.Scalar.StateBridge
