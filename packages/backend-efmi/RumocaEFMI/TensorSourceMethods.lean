import RumocaEFMI.TensorAlgorithmProofs
import RumocaEFMI.TensorProductionProofs
import RumocaEFMI.TensorStartup
import RumocaEFMI.TensorMethodEntry
import RumocaCore.GALEC.Elaboration.Initialization.Body
import RumocaCore.GALEC.Elaboration.Square.Finite
import RumocaCore.GALEC.Elaboration.Layout.State

/-! Original tensor Algorithm Code methods composed with the emitted Production
C methods on the one production function table. Each correspondence fixes a
selected original method of the one-pass source pipeline before runtime values;
source execution and the public C call share the same final heap. This is a
single-call relation per method, not an FMI scheduler, a normative lifecycle or
input policy, or independent file evidence. No backend name resolution, shape
inference or tensor-cell enumeration is introduced. -/
noncomputable section
namespace Rumoca.EFMI.TensorSourceMethods
open Rumoca.Tensor Rumoca.Solve Rumoca.Solve.Tensor
open GALEC GALEC.Elaboration GALEC.VectorBodies
open CTree CMemory CMemory.TensorView CDeclaredMembers CDeclaredMembers.MemberStorage
open TensorProduction TensorPublicStorage TensorNumericalLinkage TensorAlgorithm
open CContextMachine TensorContextCalls

/-! ### Numerical observations of the later-method layout -/

abbrev InputEnv := Env Binary64.Value (Layout.inputShapes (Square.squareFields squareExtent))
abbrev OutputEnv := Env Binary64.Value (Layout.outputShapes (Square.squareFields squareExtent))

/-- The original DoStep body reads only `u` and overwrites `x` and `J`. This
view records those numerical members; it does not invent a finite clock. -/
structure NumericalView (heap : Heap) (base : Address) (input : InputEnv) (state : OutputEnv) : Prop where
  input : Reads heap (base.member inputVar.name) (input (Square.squareInput squareExtent))
  rhs : Reads heap (base.member squareVar.name) (state (Square.squareRhs squareExtent))
  jacobian : Reads heap (base.member jacobianVar.name) (state (Square.squareJacobian squareExtent))

theorem vector_index_two (index : Fin 2) : vectorIndex index = index :=
  Fin.ext (Coordinate.vector index)

/-- Change only the coordinate view, retaining exact finite encodings. -/
theorem prepared_results (input : InputEnv) (env : IteratorEnv [])
    (before after : OutputEnv)
    (executed : (SquareBodies.body (Square.squareInput squareExtent) (Square.squareRhs squareExtent)
      (Square.squareJacobian squareExtent)).Executes
      Finite.Result Binary64.positiveZero Binary64.one @input @env @before @after) :
    Finite.Executes (ArrayProfile.squareProgram inputShape)
      (ArrayProfile.environment (input (Square.squareInput squareExtent))
        (input (Square.squareInput squareExtent)))
      (after (Square.squareRhs squareExtent)) ∧
    after (Square.squareJacobian squareExtent) =
      (ArrayProfile.squareJacobianProgram inputShape).eval Finite.ops Binary64.positiveZero Binary64.one
        (ArrayProfile.environment (input (Square.squareInput squareExtent))
          (input (Square.squareInput squareExtent))) := by
  obtain ⟨rhs, run, rhsValue, jacobianValue, _⟩ :=
    SquareBodies.body_outputs (Square.squareInput squareExtent) (Square.squareRhs squareExtent)
      (Square.squareJacobian squareExtent)
      (input (Square.squareInput squareExtent)) @input @env @before @after executed
  refine ⟨rhsValue ▸ run, ?_⟩
  apply (matrixEquiv (rows := 2) (columns := 2)).injective
  funext row col
  simpa only [squareExtent, ArrayProfile.stateShape, List.headD_cons, matrixEquiv, Value.toMatrix,
    Matrix.of_apply, vector_index_two] using
    jacobianValue row col

/-! ### Startup source initialization and the emitted Startup body -/

/-- The heap reads exactly the source post-values of `x`, `J` and the period. -/
def Observes (heap : Heap) (base : Address) (after : Env Binary64.Value outputs)
    (vector : Ref outputs ⟨[squareExtent]⟩) (matrix : Ref outputs (matrixShape squareExtent squareExtent))
    (period : Ref outputs scalar) : Prop :=
  Reads heap (base.member squareVar.name) (after vector) ∧
  Reads heap (base.member jacobianVar.name) (after matrix) ∧
  Reads heap (base.member clockName) (after period)

/-- The emitted Startup body returns status zero with the owned Startup outcome
and a final heap that observes the given source post-values. -/
def Completes (unusedKernel : CSyntax.Program) (objects : Objects)
    (heap : Heap) (base : Address) (after : Env Binary64.Value outputs)
    (vector : Ref outputs ⟨[squareExtent]⟩) (matrix : Ref outputs (matrixShape squareExtent squareExtent))
    (period : Ref outputs scalar) (locals : CBody.Locals) (types : CLoops.Types)
    (stack : CCalls.Typed.Continuation) : Prop :=
  letI : CInterface := NumericalInterface.interface
  ∃ finalHeap, AllocatedMethods.StartupOutcome objects heap finalHeap base ∧
    Observes finalHeap base @after vector matrix period ∧
    Transition.Reaches (machine (expressions objects) (program unusedKernel)).step
      (.body (.running startupFunction.body locals types heap) statusAlias stack)
      (.returning (.integer 0) finalHeap stack)

/-- The source post-values need no heap representation of the old outputs:
the Startup body reads none of them. -/
theorem initialized_to_c (unusedKernel : CSyntax.Program) (objects : Objects)
    (heap : Heap) (base : Address) (before after : Env Binary64.Value outputs)
    (vector : Ref outputs ⟨[squareExtent]⟩) (matrix : Ref outputs (matrixShape squareExtent squareExtent))
    (period : Ref outputs scalar)
    (initialized : InitializationBodies.Initializes vector matrix period
      Binary64.positiveZero Binary64.one @before @after)
    (storage : AllocatedStorage objects heap base)
    (locals : CBody.Locals) (types : CLoops.Types)
    (bound : locals "self" = some (.pointer (some base)))
    (unshadowed : locals "rumoca_initialize" = none)
    (stack : CCalls.Typed.Continuation) :
    Completes unusedKernel objects heap base @after vector matrix period locals types stack := by
  letI : CInterface := NumericalInterface.interface
  obtain ⟨finalHeap, outcome, ran⟩ := AllocatedMethods.startup_body unusedKernel objects heap base
    storage locals types bound unshadowed stack
  refine ⟨finalHeap, outcome, ⟨?_, ?_, ?_⟩, ran⟩
  · rw [initialized.1]
    exact outcome.square
  · rw [initialized.2.1]
    exact outcome.jacobian
  · rw [initialized.2.2.1]
    intro i
    have zero : i.val = 0 := by have := i.isLt; change i.val < 1 at this; omega
    simpa only [Fin.getElem_fin, zero, Address.index_zero, Tensor.Value.getElem_fill] using outcome.clock

/-! ### Startup correspondence on the public entry -/

/-- The selected original Startup method and the public Startup call on the
production table: source execution exists from every pre-state and its
post-values are read from the very final heap of the call. -/
def StartupCorrespondence (model : TensorModel ArrayProfile.stateShape) (algorithm : String) : Prop :=
  ∃ product method,
    Block.fromSource algorithm = .ok product ∧
    SourceContract squareExtent Static.Bounded.integerCeiling product.parsed.ast model.kernel ∧
    Methods.Headers.Selects (.ident "Startup") product.parsed.ast.methods method ∧
    ∀ (unusedKernel : CSyntax.Program) (objects : Objects) (heap : Heap) (base : Address)
      (input : Env Binary64.Value (Layout.inputShapes (Square.startupFields squareExtent)))
      (env : IteratorEnv [])
      (before : Env Binary64.Value (Layout.outputShapes (Square.startupFields squareExtent))),
      AllocatedStorage objects heap base →
      ∃ (after : Env Binary64.Value (Layout.outputShapes (Square.startupFields squareExtent)))
        (finalHeap : Heap),
        SourceExec (Square.startupFields squareExtent) Static.Bounded.integerCeiling
          product.parsed.ast method Finite.Result Binary64.positiveZero Binary64.one
          @input @env @before @after ∧
        AllocatedMethods.StartupOutcome objects heap finalHeap base ∧
        Observes finalHeap base @after (Square.startupRhs squareExtent)
          (Square.startupJacobian squareExtent) (Square.startupPeriod squareExtent) ∧
        ContextMethod.Completes (program unusedKernel) objects startupName heap finalHeap base

/-- Original source execution is constructed from the mandatory source-body
semantics, and the observed final heap is the very heap of the public call.
There is no external parse, lowering, source execution or C entry premise. -/
theorem algorithm_startup_correspondence (algorithmContract : AlgorithmContract model algorithm) :
    StartupCorrespondence model algorithm := by
  obtain ⟨product, compiled, sourceContract⟩ := algorithmContract.original_source
  obtain ⟨startup, recalibrate, doStep, selected, _, _, initialization, _, _, _⟩ :=
    sourceContract.original
  refine ⟨product, startup, compiled, sourceContract, selected, ?_⟩
  intro unusedKernel objects heap base input env before storage
  let after : Env Binary64.Value (Layout.outputShapes (Square.startupFields squareExtent)) :=
    InitializationBodies.updated (Square.startupRhs squareExtent) (Square.startupJacobian squareExtent)
      (Square.startupPeriod squareExtent) Binary64.positiveZero Binary64.one @before
  have initialized : InitializationBodies.Initializes (Square.startupRhs squareExtent)
      (Square.startupJacobian squareExtent) (Square.startupPeriod squareExtent)
      Binary64.positiveZero Binary64.one @before @after :=
    (InitializationBodies.initializes_iff_update _ _ _ _ _ @before @after).mpr rfl
  have executed := (initialization Finite.Result Binary64.positiveZero Binary64.one
    @input @env @before @after).mpr initialized
  obtain ⟨finalHeap, outcome, observed, ran⟩ := initialized_to_c
    unusedKernel objects heap base @before @after (Square.startupRhs squareExtent)
    (Square.startupJacobian squareExtent) (Square.startupPeriod squareExtent) initialized storage
    (ContextMethod.locals base) ContextMethod.types rfl rfl .done
  rw [AllocatedMethods.startup_method] at ran
  have member : startupFunction ∈ TensorProduction.functions := by
    simp [TensorProduction.functions]
  rw [AllocatedMethods.startup_method] at member
  exact ⟨@after, finalHeap, executed, outcome, observed,
    AllocatedMethods.complete unusedKernel objects startupName _ member heap finalHeap base ran⟩

/-- The Algorithm bytes, the Production C contract and their composed Startup
correspondence on the same bytes. -/
structure StartupContract (model : TensorModel ArrayProfile.stateShape)
    (algorithmBytes productionC : String) : Prop where
  algorithm : AlgorithmContract model algorithmBytes
  target : TensorProduction.Contract productionC
  correspondence : StartupCorrespondence model algorithmBytes

theorem startup_contract (algorithm : AlgorithmContract model algorithmBytes)
    (target : TensorProduction.Contract productionC) :
    StartupContract model algorithmBytes productionC :=
  ⟨algorithm, target, algorithm_startup_correspondence algorithm⟩

/-! ### Recalibrate: all four logical fields preserved -/

def periodRef : Ref (Layout.inputShapes (Square.squareFields squareExtent)) scalar := .there .here

/-- Complete logical field observations for the later-method layout. Physical
allocation and status are separately retained by the target outcome. -/
structure StateView (heap : Heap) (base : Address) (input : InputEnv) (state : OutputEnv) : Prop where
  numerical : NumericalView heap base @input @state
  period : Reads heap (base.member clockName) (input periodRef)

theorem preserved (outcome : AllocatedMethods.RecalibrateOutcome objects heap after base)
    (view : StateView heap base @input @state) : StateView after base @input @state := by
  refine ⟨⟨reads_framed view.numerical.input outcome.input,
    reads_framed view.numerical.rhs outcome.square,
    reads_framed view.numerical.jacobian outcome.jacobian⟩, ?_⟩
  apply reads_framed view.period
  intro i
  apply outcome.frame
  simpa only [Address.index_zero] using
    (Address.fields_separate base clockName statusName (by decide +kernel) i 0)

/-- The selected original Recalibrate method leaves every source field
unchanged, and the public Recalibrate call preserves the view of all four. -/
def RecalibrateCorrespondence (model : TensorModel ArrayProfile.stateShape) (algorithm : String) : Prop :=
  ∃ product method,
    Block.fromSource algorithm = .ok product ∧
    SourceContract squareExtent Static.Bounded.integerCeiling product.parsed.ast model.kernel ∧
    Methods.Headers.Selects (.ident "Recalibrate") product.parsed.ast.methods method ∧
    ∀ (unusedKernel : CSyntax.Program) (objects : Objects) (heap : Heap) (base : Address)
      (input : InputEnv) (env : IteratorEnv []) (before : OutputEnv),
      AllocatedStorage objects heap base → StateView heap base @input @before →
      SourceExec (Square.squareFields squareExtent) Static.Bounded.integerCeiling product.parsed.ast
        method Finite.Result Binary64.positiveZero Binary64.one @input @env @before @before ∧
      AllocatedMethods.RecalibrateOutcome objects heap (cleared heap base) base ∧
      StateView (cleared heap base) base @input @before ∧
      ContextMethod.Completes (program unusedKernel) objects recalibrateName heap (cleared heap base) base

theorem recalibrate_correspondence (algorithmContract : AlgorithmContract model algorithm) :
    RecalibrateCorrespondence model algorithm := by
  obtain ⟨product, parsed, sourceContract⟩ := algorithmContract.original_source
  obtain ⟨startup, recalibrate, doStep, _, selected, _, _, semantics, _, _⟩ := sourceContract.original
  refine ⟨product, recalibrate, parsed, sourceContract, selected, ?_⟩
  intro unusedKernel objects heap base input env before storage view
  obtain ⟨outcome, completed⟩ := AllocatedMethods.recalibrate unusedKernel objects heap base storage
  exact ⟨(semantics Finite.Result Binary64.positiveZero Binary64.one
    @input @env @before @before).mpr rfl, outcome, preserved outcome view, completed⟩

/-! ### Startup to later-method handoff -/

/-- Re-partition the Startup layout into the later-method layout. The
transport is whole-shaped; no tensor cell is enumerated. -/
def handoff
    (input : Env α (Layout.inputShapes (Square.startupFields squareExtent)))
    (output : Env α (Layout.outputShapes (Square.startupFields squareExtent))) :
    Env α (Layout.inputShapes (Square.squareFields squareExtent)) ×
      Env α (Layout.outputShapes (Square.squareFields squareExtent)) :=
  Layout.State.repartition
    (show (Square.startupFields squareExtent).map Layout.Field.declaration =
      (Square.squareFields squareExtent).map Layout.Field.declaration from rfl) @input @output

theorem startup_ready
    (input : Env Binary64.Value (Layout.inputShapes (Square.startupFields squareExtent)))
    (output : Env Binary64.Value (Layout.outputShapes (Square.startupFields squareExtent)))
    (storage : Storage objects heap base (input .here))
    (outcome : AllocatedMethods.StartupOutcome objects heap after base)
    (observed : Observes after base @output (Square.startupRhs squareExtent)
      (Square.startupJacobian squareExtent) (Square.startupPeriod squareExtent)) :
    Storage objects after base ((handoff @input @output).1 (Square.squareInput squareExtent)) ∧
    StateView after base (handoff @input @output).1 (handoff @input @output).2 := by
  have finalStorage := outcome.storage.with_input (storage.inputCells.framed outcome.input)
  exact ⟨finalStorage, ⟨⟨finalStorage.input_reads, observed.1, observed.2.1⟩, observed.2.2⟩⟩

/-- Finite represented input storage is an explicit stronger entry premise for
this handoff, not an input-write policy or a change to allocated-only Startup. -/
def StartupReady (model : TensorModel ArrayProfile.stateShape) (algorithm : String) : Prop :=
  ∃ product method,
    Block.fromSource algorithm = .ok product ∧
    SourceContract squareExtent Static.Bounded.integerCeiling product.parsed.ast model.kernel ∧
    Methods.Headers.Selects (.ident "Startup") product.parsed.ast.methods method ∧
    ∀ (unusedKernel : CSyntax.Program) (objects : Objects) (heap : Heap) (base : Address)
      (input : Env Binary64.Value (Layout.inputShapes (Square.startupFields squareExtent)))
      (env : IteratorEnv [])
      (before : Env Binary64.Value (Layout.outputShapes (Square.startupFields squareExtent))),
      Storage objects heap base (input .here) →
      ∃ (after : Env Binary64.Value (Layout.outputShapes (Square.startupFields squareExtent)))
        (finalHeap : Heap),
        SourceExec (Square.startupFields squareExtent) Static.Bounded.integerCeiling
          product.parsed.ast method Finite.Result Binary64.positiveZero Binary64.one
          @input @env @before @after ∧
        AllocatedMethods.StartupOutcome objects heap finalHeap base ∧
        ContextMethod.Completes (program unusedKernel) objects startupName heap finalHeap base ∧
        Storage objects finalHeap base ((handoff @input @after).1 (Square.squareInput squareExtent)) ∧
        StateView finalHeap base (handoff @input @after).1 (handoff @input @after).2

theorem source_startup_ready (correspondence : StartupCorrespondence model algorithm) :
    StartupReady model algorithm := by
  obtain ⟨product, method, parsed, sourceContract, selected, runs⟩ := correspondence
  refine ⟨product, method, parsed, sourceContract, selected, ?_⟩
  intro unusedKernel objects heap base input env before storage
  obtain ⟨after, finalHeap, sourceRan, outcome, observed, publicRan⟩ :=
    runs unusedKernel objects heap base @input @env @before storage.toAllocated
  obtain ⟨finalStorage, finalView⟩ := startup_ready @input @after storage outcome observed
  exact ⟨@after, finalHeap, sourceRan, outcome, publicRan, finalStorage, finalView⟩

/-! ### DoStep: the same original body and the same post-store -/

theorem original_step {block : AST.Block} {method : AST.Method}
    (sourceContract : SourceContract squareExtent ceiling block kernel)
    (selected : Methods.Headers.Selects (.ident "DoStep") block.methods method)
    (unusedKernel : CSyntax.Program) (objects : Objects) (heap : Heap) (base : Address)
    (input : InputEnv) (env : IteratorEnv []) (before after : OutputEnv)
    (storage : Storage objects heap base (input (Square.squareInput squareExtent)))
    (period : Reads heap (base.member clockName) (input periodRef))
    (executed : SourceExec (Square.squareFields squareExtent) ceiling block method Finite.Result
      Binary64.positiveZero Binary64.one @input @env @before @after) :
    ∃ finalHeap,
      ContextDoStep.Outcome objects heap finalHeap base (input (Square.squareInput squareExtent))
        (after (Square.squareRhs squareExtent))
        (ContextMethod.coefficients (input (Square.squareInput squareExtent))) ∧
      StateView finalHeap base @input @after ∧
      ContextMethod.Completes (program unusedKernel) objects doStepName heap finalHeap base := by
  obtain ⟨interface, prepared⟩ := sourceContract.prepared
  have lowered := (Methods.Correspondence.selected_execution prepared.doStep selected
    Finite.Result Binary64.positiveZero Binary64.one @input @env @before @after).mp executed
  have bodyRan := (Square.square_equivalent (Square.squareInput squareExtent)
    (Square.squareRhs squareExtent) (Square.squareJacobian squareExtent) Finite.Result
    Binary64.positiveZero Binary64.one @input @env @before @after).mp lowered
  obtain ⟨rhsRan, jacobian⟩ := prepared_results @input @env @before @after bodyRan
  obtain ⟨finalHeap, outcome, completed⟩ := ContextMethod.doStep_from_rhs_in
    (program unusedKernel) (numerical_in_actual unusedKernel)
    (method_defined unusedKernel doStepFunction (by simp [TensorProduction.functions]))
    objects heap base (input (Square.squareInput squareExtent))
    (after (Square.squareRhs squareExtent)) storage rhsRan
  refine ⟨finalHeap, outcome, ⟨⟨outcome.storage.input_reads, outcome.square, ?_⟩, ?_⟩, completed⟩
  · rw [jacobian]
    exact outcome.jacobian
  · intro i
    have zero : i.val = 0 := by have bound := i.isLt; change i.val < 1 at bound; omega
    simpa only [zero, Address.index_zero, load, outcome.clock] using period i

/-- The selected original DoStep method and the public DoStep call: every
source execution from a represented finite input is matched by one public call
whose final heap views the same source post-store. -/
def StepCorrespondence (model : TensorModel ArrayProfile.stateShape) (algorithm : String) : Prop :=
  ∃ product method,
    Block.fromSource algorithm = .ok product ∧
    SourceContract squareExtent Static.Bounded.integerCeiling product.parsed.ast model.kernel ∧
    Methods.Headers.Selects (.ident "DoStep") product.parsed.ast.methods method ∧
    ∀ (unusedKernel : CSyntax.Program) (objects : Objects) (heap : Heap) (base : Address)
      (input : InputEnv) (env : IteratorEnv []) (before after : OutputEnv),
      Storage objects heap base (input (Square.squareInput squareExtent)) →
      Reads heap (base.member clockName) (input periodRef) →
      SourceExec (Square.squareFields squareExtent) Static.Bounded.integerCeiling product.parsed.ast
        method Finite.Result Binary64.positiveZero Binary64.one @input @env @before @after →
      ∃ finalHeap,
        ContextDoStep.Outcome objects heap finalHeap base (input (Square.squareInput squareExtent))
          (after (Square.squareRhs squareExtent))
          (ContextMethod.coefficients (input (Square.squareInput squareExtent))) ∧
        StateView finalHeap base @input @after ∧
        ContextMethod.Completes (program unusedKernel) objects doStepName heap finalHeap base

theorem step_correspondence (algorithmContract : AlgorithmContract model algorithm) :
    StepCorrespondence model algorithm := by
  obtain ⟨product, parsed, sourceContract⟩ := algorithmContract.original_source
  obtain ⟨startup, recalibrate, doStep, _, _, selected, _⟩ := sourceContract.original
  exact ⟨product, doStep, parsed, sourceContract, selected, original_step sourceContract selected⟩

/-- All three original method correspondences and the represented-input
Startup handoff on one Algorithm/Production byte pair. This does not assert an
FMI scheduler, a normative lifecycle or input policy, or independent file bytes. -/
structure MethodsContract (model : TensorModel ArrayProfile.stateShape)
    (algorithmBytes productionC : String) : Prop where
  startup : StartupContract model algorithmBytes productionC
  recalibrate : RecalibrateCorrespondence model algorithmBytes
  ready : StartupReady model algorithmBytes
  doStep : StepCorrespondence model algorithmBytes

theorem methods_correct (algorithm : AlgorithmContract model algorithmBytes)
    (target : TensorProduction.Contract productionC) :
    MethodsContract model algorithmBytes productionC :=
  ⟨startup_contract algorithm target, recalibrate_correspondence algorithm,
    source_startup_ready (algorithm_startup_correspondence algorithm), step_correspondence algorithm⟩

end Rumoca.EFMI.TensorSourceMethods
