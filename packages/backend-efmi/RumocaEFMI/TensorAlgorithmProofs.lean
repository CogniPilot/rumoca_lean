import RumocaEFMI.TensorAlgorithmCode
import RumocaCore.GALEC.Elaboration.Block.Source
import GALECParser.Certificate

/-! Original-body semantics of the emitted tensor Algorithm Code. The source
contract is derived for any block that prepares, through the generic whole-block
preparer, to the square profile result; it does not parse a profile name or
recognize a source fixture. The emitted text is certified to parse to the
emitter's tree, which prepares under the target Integer ceiling. -/
noncomputable section
namespace Rumoca.EFMI.TensorAlgorithm
open Rumoca.Tensor Rumoca.Solve Rumoca.Solve.Tensor
open GALEC GALEC.Elaboration GALEC.Coefficients GALEC.VectorBodies

def startupResult (extent : Nat) : Methods.Preparation.Result :=
  ⟨Square.startupFields extent, Initialization.Body.lowered
    (Square.startupRhs extent) (Square.startupJacobian extent) (Square.startupPeriod extent)⟩

def recalibrateResult (extent : Nat) : Methods.Preparation.Result :=
  ⟨Square.squareFields extent, .skip⟩

def stepResult (extent : Nat) : Methods.Preparation.Result :=
  ⟨Square.squareFields extent, Square.loweredSquare
    (Square.squareInput extent) (Square.squareRhs extent) (Square.squareJacobian extent)⟩

def preparedResult (extent : Nat) (interface : Block.Headers.Interface) : Block.Result :=
  ⟨interface, startupResult extent, recalibrateResult extent, stepResult extent⟩

def SourceExec (fields : List Layout.Field) (ceiling : Nat) (block : AST.Block)
    (method : AST.Method) (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes fields)) (env : IteratorEnv [])
    (before after : Env α (Layout.outputShapes fields)) : Prop :=
  Bodies.Source.statements (Layout.bindings fields)
    (Declarations.ShapeLookup.HasShape ceiling block.declarations) ceiling step zero one
    @input .nil @env method.body @before @after

def StartupSemantics (extent ceiling : Nat) (block : AST.Block) (method : AST.Method) : Prop :=
  ∀ {α : Type} (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes (Square.startupFields extent))) (env : IteratorEnv [])
    (before after : Env α (Layout.outputShapes (Square.startupFields extent))),
    SourceExec (Square.startupFields extent) ceiling block method step zero one
      @input @env @before @after ↔
      InitializationBodies.Initializes (Square.startupRhs extent)
        (Square.startupJacobian extent) (Square.startupPeriod extent) zero one @before @after

def RecalibrateSemantics (extent ceiling : Nat) (block : AST.Block) (method : AST.Method) : Prop :=
  ∀ {α : Type} (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes (Square.squareFields extent))) (env : IteratorEnv [])
    (before after : Env α (Layout.outputShapes (Square.squareFields extent))),
    SourceExec (Square.squareFields extent) ceiling block method step zero one
      @input @env @before @after ↔ @after = @before

def StepSemantics (extent ceiling : Nat) (block : AST.Block) (method : AST.Method)
    (kernel : PointwiseIVP ⟨[extent]⟩) : Prop :=
  ∀ (state : Value Binary64.Value ⟨[extent]⟩)
    (input : Env Binary64.Value (Layout.inputShapes (Square.squareFields extent))) (env : IteratorEnv [])
    (before after : Env Binary64.Value (Layout.outputShapes (Square.squareFields extent))),
    SourceExec (Square.squareFields extent) ceiling block method Finite.Result
      Binary64.positiveZero Binary64.one @input @env @before @after ↔
      ∃ rhs, Finite.Executes kernel.derivative
        (ArrayProfile.environment state (input (Square.squareInput extent))) rhs ∧
        @after = @Env.update Binary64.Value _ (matrixShape extent extent)
          (Env.update @before (Square.squareRhs extent) rhs) (Square.squareJacobian extent)
          (diagonalValue Finite.ops Binary64.positiveZero Binary64.one doubledInput
            (input (Square.squareInput extent)))

def ADSemantics (extent ceiling : Nat) (block : AST.Block) (method : AST.Method)
    (kernel : PointwiseIVP ⟨[extent]⟩) : Prop :=
  ∀ (state : Value Binary64.Value ⟨[extent]⟩)
    (input : Env Binary64.Value (Layout.inputShapes (Square.squareFields extent))) (env : IteratorEnv [])
    (before after : Env Binary64.Value (Layout.outputShapes (Square.squareFields extent))),
    SourceExec (Square.squareFields extent) ceiling block method Finite.Result
      Binary64.positiveZero Binary64.one @input @env @before @after →
      ∃ diagonal, kernel.diagonal = some diagonal ∧ ∀ row col : Fin extent,
        (after (Square.squareJacobian extent))[matrixIndex (row, col)] =
          (diagonal.eval Finite.ops Binary64.positiveZero Binary64.one
            (ArrayProfile.environment state (input (Square.squareInput extent)))).toMatrix
              (vectorIndex row) (vectorIndex col)

/-- Every method and its original body are fixed before runtime choices.
Startup specifies zero x/J and one period; DoStep retains the original finite
primal domain, exact whole-store updates and the prepared AD matrix. -/
structure SourceContract (extent ceiling : Nat) (block : AST.Block)
    (kernel : PointwiseIVP ⟨[extent]⟩) : Prop where
  prepared : ∃ interface, Block.Prepares ceiling block (preparedResult extent interface)
  kernel_profile : kernel = squareKernel ⟨[extent]⟩
  original : ∃ startup recalibrate doStep,
    Methods.Headers.Selects (.ident "Startup") block.methods startup ∧
    Methods.Headers.Selects (.ident "Recalibrate") block.methods recalibrate ∧
    Methods.Headers.Selects (.ident "DoStep") block.methods doStep ∧
    StartupSemantics extent ceiling block startup ∧
    RecalibrateSemantics extent ceiling block recalibrate ∧
    StepSemantics extent ceiling block doStep kernel ∧ ADSemantics extent ceiling block doStep kernel

theorem source_contract
    (prepared : Block.Prepares ceiling block (preparedResult extent interface))
    (profile : kernel = squareKernel ⟨[extent]⟩) : SourceContract extent ceiling block kernel := by
  subst kernel
  refine ⟨⟨interface, prepared⟩, rfl, interface.startup, interface.recalibrate, interface.doStep,
    prepared.headers.startup, prepared.headers.recalibrate, prepared.headers.doStep, ?_, ?_, ?_, ?_⟩
  · intro α step zero one input env before after
    exact (Methods.Correspondence.selected_execution prepared.startup prepared.headers.startup
      step zero one @input @env @before @after).trans
      ((Initialization.Body.equivalent (Square.startupRhs extent)
        (Square.startupJacobian extent) (Square.startupPeriod extent)
        step zero one @input @env @before @after).trans
        (InitializationBodies.body_executes_iff (Square.startupRhs extent)
          (Square.startupJacobian extent) (Square.startupPeriod extent)
          step zero one @input @env @before @after))
  · intro α step zero one input env before after
    exact Methods.Correspondence.selected_execution prepared.recalibrate prepared.headers.recalibrate
      step zero one @input @env @before @after
  · intro state input env before after
    exact (Methods.Correspondence.selected_execution prepared.doStep prepared.headers.doStep
      Finite.Result Binary64.positiveZero Binary64.one @input @env @before @after).trans
      ((Square.square_equivalent (Square.squareInput extent) (Square.squareRhs extent)
        (Square.squareJacobian extent) Finite.Result Binary64.positiveZero Binary64.one
        @input @env @before @after).trans
        (SquareBodies.body_executes (Square.squareInput extent) (Square.squareRhs extent)
          (Square.squareJacobian extent) state @input @env @before @after))
  · intro state input env before after executed
    have lowered := (Methods.Correspondence.selected_execution prepared.doStep prepared.headers.doStep
      Finite.Result Binary64.positiveZero Binary64.one @input @env @before @after).mp executed
    have body := (Square.square_equivalent (Square.squareInput extent) (Square.squareRhs extent)
      (Square.squareJacobian extent) Finite.Result Binary64.positiveZero Binary64.one
      @input @env @before @after).mp lowered
    obtain ⟨_, _, _, observed, _⟩ := SquareBodies.body_outputs (Square.squareInput extent)
      (Square.squareRhs extent) (Square.squareJacobian extent) state @input @env @before @after body
    exact ⟨ArrayProfile.squareJacobianProgram ⟨[extent]⟩, rfl, observed⟩

/-- The three selected methods of the emitted tensor square block. -/
def interface : Block.Headers.Interface :=
  ⟨"TensorSquare", squareStartup, Scalar.recalibrateMethod, squareDoStep⟩

/-- The emitter's block prepares to the square profile result for every
positive extent within the ceiling; the extent is never enumerated. -/
theorem square_prepared (positive : 0 < extent) (within : extent ≤ ceiling)
    (axisBound : 2 ≤ ceiling) :
    Block.Prepares ceiling (squareBlock extent) (preparedResult extent interface) := by
  have declared := Square.square_declared positive within
  refine ⟨(Block.Headers.read_iff _ _).mp rfl, ?_, ?_, ?_⟩
  · exact .body ((Methods.Headers.select_iff _ _ _).mp rfl) declared
      ((Layout.body_iff _ (Methods.Preparation.declared_fields _ declared) _ _).mp
        (Square.startup_lowered positive within axisBound))
  · show Methods.Preparation.Prepares _ Capabilities.DoStep.role ceiling (squareBlock extent)
      ⟨Capabilities.Generic.fields Capabilities.DoStep.role
        ((Square.squareFields extent).map Layout.Field.declaration), .skip⟩
    exact .body ((Methods.Headers.select_iff _ _ _).mp rfl) declared .nil
  · show Methods.Preparation.Prepares _ Capabilities.DoStep.role ceiling (squareBlock extent)
      ⟨Capabilities.Generic.fields Capabilities.DoStep.role
        ((Square.squareFields extent).map Layout.Field.declaration),
        Square.loweredSquare (Square.squareInput extent) (Square.squareRhs extent)
          (Square.squareJacobian extent)⟩
    exact .body ((Methods.Headers.select_iff _ _ _).mp rfl) declared ((Layout.body_iff _ (Methods.Preparation.declared_fields Capabilities.DoStep.role
        declared) _ _).mp (Square.layout_body_lowered positive within axisBound))

theorem prepared : Block.Prepares Static.Bounded.integerCeiling (squareBlock squareExtent)
    (preparedResult squareExtent interface) :=
  square_prepared (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/- Kernel-checked parse of the emitted tensor Algorithm Code text. -/
certify_source square tensorAlgorithmSource

/-- The parsed tree of the emitted text is exactly the emitter's tree. -/
theorem square_ast : square.ast = squareBlock squareExtent := rfl

theorem emitted_parses :
    ∃ parsed, Syntax.parse tensorAlgorithmSource = .ok parsed ∧
      parsed.ast = squareBlock squareExtent := by
  obtain ⟨parsed, accepted, same⟩ := square.parsed
  exact ⟨parsed, accepted, same.trans square_ast⟩

theorem emitted_prepared :
    ∃ product, Block.fromSource tensorAlgorithmSource = .ok product ∧
      product.result = preparedResult squareExtent interface :=
  (Block.fromSource_iff _ _).mpr ⟨squareBlock squareExtent, square_ast ▸ square.witness, prepared⟩

/-- Predicate on the supplied Algorithm bytes: they are the emitted text, which
parses to the emitter's tree, and the one-pass source pipeline returns an
original AST whose three bodies satisfy the source contract. No original-body
execution premise is supplied by the checker. -/
structure AlgorithmContract (model : TensorModel ArrayProfile.stateShape) (emitted : String) : Prop where
  bytes : tensorAlgorithmSource = emitted
  parsed : ∃ parsed, Syntax.parse emitted = .ok parsed ∧ parsed.ast = squareBlock squareExtent
  original_source : ∃ product,
    Block.fromSource emitted = .ok product ∧
    SourceContract squareExtent Static.Bounded.integerCeiling product.parsed.ast model.kernel

theorem algorithm_correct (model : TensorModel ArrayProfile.stateShape)
    (printed : tensorAlgorithmSource = emitted) : AlgorithmContract model emitted := by
  subst emitted
  obtain ⟨product, compiled, sameResult⟩ := emitted_prepared
  exact ⟨rfl, emitted_parses, product, compiled,
    source_contract (sameResult ▸ product.prepared) model.profile⟩

end Rumoca.EFMI.TensorAlgorithm
