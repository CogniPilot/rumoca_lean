import RumocaEFMI.TensorAlgorithmCode
import RumocaCore.GALEC.Elaboration.Block.Source
import RumocaCore.GALEC.Elaboration.Square.Outcomes
import GALECParser.Certificate

/-! Original-body semantics of the emitted tensor Algorithm Code. The source
contract is derived for any block that prepares, through the generic whole-block
preparer, to the square profile result with the square signal interfaces; it
does not parse a profile name or recognize a source fixture. The emitted text is
certified to parse to the emitter's tree, which prepares under the target
Integer ceiling. DoStep is total over finite inputs, with the error signal
`OVERFLOW` as its only non-ordinary outcome. -/
noncomputable section
namespace Rumoca.EFMI.TensorAlgorithm
open Rumoca.Tensor Rumoca.Solve Rumoca.Solve.Tensor
open GALEC GALEC.Elaboration GALEC.Coefficients GALEC.VectorBodies

def SourceExec (fields : List Layout.Field) (ceiling : Nat) (block : AST.Block)
    (method : AST.Method) (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes fields)) (env : IteratorEnv [])
    (before after : Env α (Layout.outputShapes fields)) : Prop :=
  Bodies.Source.statements (Layout.bindings fields)
    (Declarations.ShapeLookup.HasShape ceiling block.declarations) ceiling step zero one
    @input .nil @env method.body @before @after

/-- Source execution with error signals of an original method body. -/
def SourceRuns (fields : List Layout.Field) (ceiling : Nat) (block : AST.Block)
    (method : AST.Method) (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes fields)) (env : IteratorEnv [])
    (before after : Signaled α (Layout.outputShapes fields)) : Prop :=
  Bodies.Source.runs (Layout.bindings fields)
    (Declarations.ShapeLookup.HasShape ceiling block.declarations) ceiling step finite zero one
    @input .nil @env method.body before after

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

/-- DoStep from a store with no signal set has exactly two outcomes over
finite arithmetic: every product and sum finite, no signal and the prepared
derivative and diagonal update; otherwise `OVERFLOW` and the store unchanged. -/
def StepSemantics (extent ceiling : Nat) (block : AST.Block) (method : AST.Method)
    (kernel : PointwiseIVP ⟨[extent]⟩) : Prop :=
  ∀ (state : Value Binary64.Value ⟨[extent]⟩)
    (input : Env Binary64.Value (Layout.inputShapes (Square.squareFields extent))) (env : IteratorEnv [])
    (before : Env Binary64.Value (Layout.outputShapes (Square.squareFields extent)))
    (after : Signaled Binary64.Value (Layout.outputShapes (Square.squareFields extent))),
    SourceRuns (Square.squareFields extent) ceiling block method Finite.Result (fun _ => True)
      Binary64.positiveZero Binary64.one @input @env ⟨@before, SignalSet.empty⟩ after ↔
      (Square.Checked (input (Square.squareInput extent)) ∧ after.2 = SignalSet.empty ∧
        ∃ rhs, Finite.Executes kernel.derivative
          (ArrayProfile.environment state (input (Square.squareInput extent))) rhs ∧
          @after.1 = @Env.update Binary64.Value _ (matrixShape extent extent)
            (Env.update @before (Square.squareRhs extent) rhs) (Square.squareJacobian extent)
            (diagonalValue Finite.ops Binary64.positiveZero Binary64.one doubledInput
              (input (Square.squareInput extent)))) ∨
      (¬ Square.Checked (input (Square.squareInput extent)) ∧
        after = ⟨@before, Square.overflowSet⟩)

/-- The finite DoStep outcome carries the prepared AD matrix. -/
def ADSemantics (extent ceiling : Nat) (block : AST.Block) (method : AST.Method)
    (kernel : PointwiseIVP ⟨[extent]⟩) : Prop :=
  ∀ (state : Value Binary64.Value ⟨[extent]⟩)
    (input : Env Binary64.Value (Layout.inputShapes (Square.squareFields extent))) (env : IteratorEnv [])
    (before : Env Binary64.Value (Layout.outputShapes (Square.squareFields extent)))
    (after : Signaled Binary64.Value (Layout.outputShapes (Square.squareFields extent))),
    SourceRuns (Square.squareFields extent) ceiling block method Finite.Result (fun _ => True)
      Binary64.positiveZero Binary64.one @input @env ⟨@before, SignalSet.empty⟩ after →
    Square.Checked (input (Square.squareInput extent)) →
      ∃ diagonal, kernel.diagonal = some diagonal ∧ ∀ row col : Fin extent,
        (after.1 (Square.squareJacobian extent))[matrixIndex (row, col)] =
          (diagonal.eval Finite.ops Binary64.positiveZero Binary64.one
            (ArrayProfile.environment state (input (Square.squareInput extent)))).toMatrix
              (vectorIndex row) (vectorIndex col)

/-- The signal interfaces (eFMI §3.2.5 §1.3): Startup and Recalibrate expose
nothing and DoStep exposes exactly `OVERFLOW`. -/
def Interfaced (startup recalibrate doStep : AST.Method) : Prop :=
  Reach.Exposes startup SignalSet.empty ∧ Reach.Exposes recalibrate SignalSet.empty ∧
    Reach.Exposes doStep Square.overflowSet

theorem interfaced :
    Interfaced Square.interface.startup Square.interface.recalibrate Square.interface.doStep :=
  ⟨Square.startup_exposes, Square.recalibrate_exposes, Square.step_exposes⟩

/-- Every method and its original body are fixed before runtime choices.
Startup specifies zero x/J and one period; DoStep checks every product and sum,
signals `OVERFLOW` without writes when a check fails, and otherwise retains the
exact whole-store updates and the prepared AD matrix. -/
structure SourceContract (extent ceiling : Nat) (block : AST.Block)
    (kernel : PointwiseIVP ⟨[extent]⟩) : Prop where
  prepared : ∃ interface, Block.Prepares ceiling block (Square.preparedResult extent interface)
  kernel_profile : kernel = squareKernel ⟨[extent]⟩
  original : ∃ startup recalibrate doStep,
    Methods.Headers.Selects (.ident "Startup") block.methods startup ∧
    Methods.Headers.Selects (.ident "Recalibrate") block.methods recalibrate ∧
    Methods.Headers.Selects (.ident "DoStep") block.methods doStep ∧
    StartupSemantics extent ceiling block startup ∧
    RecalibrateSemantics extent ceiling block recalibrate ∧
    StepSemantics extent ceiling block doStep kernel ∧ ADSemantics extent ceiling block doStep kernel ∧
    Interfaced startup recalibrate doStep

theorem source_contract
    (prepared : Block.Prepares ceiling block (Square.preparedResult extent interface))
    (profile : kernel = squareKernel ⟨[extent]⟩)
    (interfaces : Interfaced interface.startup interface.recalibrate interface.doStep) :
    SourceContract extent ceiling block kernel := by
  subst kernel
  refine ⟨⟨interface, prepared⟩, rfl, interface.startup, interface.recalibrate, interface.doStep,
    prepared.headers.startup, prepared.headers.recalibrate, prepared.headers.doStep, ?_, ?_, ?_, ?_,
    interfaces⟩
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
    exact (Methods.Correspondence.selected_runs prepared.doStep prepared.headers.doStep
      Finite.Result (fun _ => True) Binary64.positiveZero Binary64.one @input @env _ after).trans
      (Square.checked_outcomes (Square.squareInput extent) (Square.squareRhs extent)
        (Square.squareJacobian extent) state @input @env @before after)
  · intro state input env before after executed checked
    have lowered := (Methods.Correspondence.selected_runs prepared.doStep prepared.headers.doStep
      Finite.Result (fun _ => True) Binary64.positiveZero Binary64.one @input @env _ after).mp executed
    rcases (Square.checked_outcomes (Square.squareInput extent) (Square.squareRhs extent)
        (Square.squareJacobian extent) state @input @env @before after).mp lowered with
      ⟨_, _, rhs, ran, updated⟩ | ⟨unchecked, _⟩
    · have body := (SquareBodies.body_executes (Square.squareInput extent) (Square.squareRhs extent)
        (Square.squareJacobian extent) state @input @env @before @after.1).mpr ⟨rhs, ran, updated⟩
      obtain ⟨_, _, _, observed, _⟩ := SquareBodies.body_outputs (Square.squareInput extent)
        (Square.squareRhs extent) (Square.squareJacobian extent) state @input @env @before @after.1 body
      exact ⟨ArrayProfile.squareJacobianProgram ⟨[extent]⟩, rfl, observed⟩
    · exact absurd checked unchecked

theorem prepared : Block.Prepares Static.Bounded.integerCeiling (Square.source squareExtent)
    (Square.preparedResult squareExtent Square.interface) :=
  Square.prepared (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/- Kernel-checked parse of the emitted tensor Algorithm Code text. -/
certify_source square tensorAlgorithmSource

/-- The parsed tree of the emitted text is exactly the emitter's tree. -/
theorem square_ast : square.ast = Square.source squareExtent := rfl

theorem emitted_parses :
    ∃ parsed, Syntax.parse tensorAlgorithmSource = .ok parsed ∧
      parsed.ast = Square.source squareExtent := by
  obtain ⟨parsed, accepted, same⟩ := square.parsed
  exact ⟨parsed, accepted, same.trans square_ast⟩

theorem emitted_prepared :
    ∃ product, Block.fromSource tensorAlgorithmSource = .ok product ∧
      product.result = Square.preparedResult squareExtent Square.interface :=
  (Block.fromSource_iff _ _).mpr ⟨Square.source squareExtent, square_ast ▸ square.witness, prepared⟩

/-- Predicate on the supplied Algorithm bytes: they are the emitted text, which
parses to the emitter's tree, and the one-pass source pipeline returns an
original AST whose three bodies satisfy the source contract. No original-body
execution premise is supplied by the checker. -/
structure AlgorithmContract (model : TensorModel ArrayProfile.stateShape) (emitted : String) : Prop where
  bytes : renderTensorAlgorithm model = emitted
  parsed : ∃ parsed, Syntax.parse emitted = .ok parsed ∧ parsed.ast = Square.source squareExtent
  original_source : ∃ product,
    Block.fromSource emitted = .ok product ∧
    SourceContract squareExtent Static.Bounded.integerCeiling product.parsed.ast model.kernel

theorem algorithm_correct (model : TensorModel ArrayProfile.stateShape)
    (printed : renderTensorAlgorithm model = emitted) : AlgorithmContract model emitted := by
  subst emitted
  obtain ⟨product, compiled, sameResult⟩ := emitted_prepared
  have prepared := product.prepared
  rw [sameResult] at prepared
  exact ⟨rfl, emitted_parses, product, compiled,
    source_contract prepared model.profile interfaced⟩

/-! ### Rejected DoStep bodies

Each block below changes one part of the emitted DoStep. The first group still
parses and prepares through the generic preparer, and the source contract,
which fixes the prepared DoStep result, rejects it. The observation executes a
prepared body over natural numbers with inputs three and outputs five under
three finiteness classifications: every value finite; only values below seven
(the square nine fails); every value but six (the sum six fails). The second
group violates the signal rules and is rejected by preparation itself. -/

/-- Every stored coordinate over any output layout. -/
def outputCells : (shapes : List Shape) → Env Nat shapes → List Nat
  | [], _ => []
  | _ :: rest, env => (env .here).data.toList ++ outputCells rest (fun r => env (.there r))

/-- One execution: every output coordinate and the final status encoding. -/
def run (finite : Nat → Bool) (result : Methods.Preparation.Result) : List Nat × Nat :=
  let final := result.2.execute ⟨Nat.add, Nat.mul, Nat.sub, Nat.div, id⟩ finite 0 1
    (fun {s} _ => Value.fill s 3) IteratorEnv.empty ⟨fun {s} _ => Value.fill s 5, SignalSet.empty⟩
  (outputCells _ final.1, final.2.encode)

def observe (result : Methods.Preparation.Result) : List (List Nat × Nat) :=
  [run (fun _ => true) result, run (fun value => decide (value < 7)) result,
    run (fun value => value != 6) result]

theorem step_lowered (contract : SourceContract extent ceiling block kernel) :
    Methods.Preparation.fromBlock (.ident "DoStep") Capabilities.DoStep.role ceiling block =
      some (Square.stepResult extent) := by
  obtain ⟨interface, prepared⟩ := contract.prepared
  exact (Methods.Preparation.fromBlock_iff _ _ _ _ _).mpr prepared.doStep

/-- The emitted block with another DoStep interface and body. -/
def withDoStep (signals : List AST.Name) (body : List AST.Statement) : AST.Block :=
  { Square.source squareExtent with
    methods := [Square.startupMethod, Scalar.recalibrateMethod,
      ⟨.ident "DoStep", signals, body, .ident "DoStep"⟩] }

open GALEC.Elaboration.Surface

/-- The preflight loop with the given guards. -/
def preflightWith (guards : List AST.Statement) : AST.Statement :=
  unitLoop "k" (dimension "u" 1) guards

/-- The re-raising check with the given check body and `else` body. -/
def checkWith (reraise body : List AST.Statement) : AST.Statement :=
  .ifThen [(.signalCheck none false [Square.overflowName] none, reraise)] (some body)

def reraise : List AST.Statement := [.signal [Square.overflowName]]

/-- A finiteness test that sets no signal when it fails. -/
def unsignaledGuard (argument : AST.Expr) : AST.Statement :=
  .ifThen [(.expr (.call (.ident Names.finiteTest) [argument]), [])] (some [])

/-- The diagonal coefficient `u[k] * u[k]` in place of `u[k] + u[k]`. -/
def coefficientBody : List AST.Statement :=
  [Square.preflightSource "u", checkWith reraise
    [Square.pointwiseSource "u" "x", Square.clearSource "J",
     unitLoop "k" (dimension "u" 1)
      [.assign (stateReference "J" [iterator "k", iterator "k"]) (Square.productSource "u")]]]

/-- The checked body without the matrix clear. -/
def unclearedBody : List AST.Statement :=
  [Square.preflightSource "u", checkWith reraise
    [Square.pointwiseSource "u" "x", Square.scatterSource "u" "J"]]

/-- The product guard deleted. -/
def productUncheckedBody : List AST.Statement :=
  [preflightWith [Square.guardSource (Square.sumSource "u")],
   checkWith reraise (Square.squareSource "u" "x" "J")]

/-- The sum guard deleted. -/
def sumUncheckedBody : List AST.Statement :=
  [preflightWith [Square.guardSource (Square.productSource "u")],
   checkWith reraise (Square.squareSource "u" "x" "J")]

/-- The product guard tests `u[k]` instead of `u[k] * u[k]`. -/
def argumentBody : List AST.Statement :=
  [preflightWith [Square.guardSource (.reference (stateReference "u" [iterator "k"])),
     Square.guardSource (Square.sumSource "u")],
   checkWith reraise (Square.squareSource "u" "x" "J")]

/-- The writes moved before the checks. -/
def writesFirstBody : List AST.Statement :=
  Square.squareSource "u" "x" "J" ++
    [Square.preflightSource "u",
     .ifThen [(.signalCheck none false [Square.overflowName] none, reraise)] none]

theorem changed_rejected (body : List AST.Statement)
    (different : Option.map observe (Methods.Preparation.fromBlock (.ident "DoStep")
      Capabilities.DoStep.role Static.Bounded.integerCeiling (withDoStep [Square.overflowName] body)) ≠
      Option.map observe (some (Square.stepResult squareExtent)))
    (kernel : PointwiseIVP ⟨[squareExtent]⟩) :
    ¬ SourceContract squareExtent Static.Bounded.integerCeiling
      (withDoStep [Square.overflowName] body) kernel :=
  fun contract => different (congrArg (Option.map observe) (step_lowered contract))

theorem coefficient_rejected (kernel : PointwiseIVP ⟨[squareExtent]⟩) :
    ¬ SourceContract squareExtent Static.Bounded.integerCeiling
      (withDoStep [Square.overflowName] coefficientBody) kernel :=
  changed_rejected _ (by decide +kernel) kernel

theorem uncleared_rejected (kernel : PointwiseIVP ⟨[squareExtent]⟩) :
    ¬ SourceContract squareExtent Static.Bounded.integerCeiling
      (withDoStep [Square.overflowName] unclearedBody) kernel :=
  changed_rejected _ (by decide +kernel) kernel

theorem product_unchecked_rejected (kernel : PointwiseIVP ⟨[squareExtent]⟩) :
    ¬ SourceContract squareExtent Static.Bounded.integerCeiling
      (withDoStep [Square.overflowName] productUncheckedBody) kernel :=
  changed_rejected _ (by decide +kernel) kernel

theorem sum_unchecked_rejected (kernel : PointwiseIVP ⟨[squareExtent]⟩) :
    ¬ SourceContract squareExtent Static.Bounded.integerCeiling
      (withDoStep [Square.overflowName] sumUncheckedBody) kernel :=
  changed_rejected _ (by decide +kernel) kernel

theorem argument_rejected (kernel : PointwiseIVP ⟨[squareExtent]⟩) :
    ¬ SourceContract squareExtent Static.Bounded.integerCeiling
      (withDoStep [Square.overflowName] argumentBody) kernel :=
  changed_rejected _ (by decide +kernel) kernel

theorem writes_first_rejected (kernel : PointwiseIVP ⟨[squareExtent]⟩) :
    ¬ SourceContract squareExtent Static.Bounded.integerCeiling
      (withDoStep [Square.overflowName] writesFirstBody) kernel :=
  changed_rejected _ (by decide +kernel) kernel

/-- Every changed block of the first group prepares generically, so its
rejection is by the source contract and not by preparation. -/
theorem changed_bodies_prepare :
    [coefficientBody, unclearedBody, productUncheckedBody, sumUncheckedBody, argumentBody,
      writesFirstBody].all (fun body =>
        (Block.fromBlock Static.Bounded.integerCeiling (withDoStep [Square.overflowName] body)).isSome) =
      true := by
  decide +kernel

/-! The second group: signal rules enforced by preparation. -/

/-- The guards' `signal OVERFLOW` deleted: the check tests a signal that
cannot be set (§1.4). -/
def unsignaledBody : List AST.Statement :=
  [preflightWith [unsignaledGuard (Square.productSource "u"), unsignaledGuard (Square.sumSource "u")],
   checkWith reraise (Square.squareSource "u" "x" "J")]

/-- The re-raise deleted: `OVERFLOW` no longer reaches the method exit (§1.3). -/
def unraisedBody : List AST.Statement :=
  [Square.preflightSource "u", checkWith [] (Square.squareSource "u" "x" "J")]

/-- Each error-signal check form other than `signal in S1, ..., Sn`, a
user-defined signal name and a Boolean condition other than `isFinite`. -/
def checkFormBody (test : AST.Condition) : List AST.Statement :=
  [Square.preflightSource "u",
   .ifThen [(test, reraise)] (some (Square.squareSource "u" "x" "J"))]

def rejectedChecks : List AST.Condition :=
  [.signalCheck (some (.ident "closure")) false [Square.overflowName] none,
   .signalCheck none true [Square.overflowName] none,
   .signalCheck none false [] none,
   .signalCheck none false [Square.overflowName] (some (Square.sumSource "u")),
   .signalCheck none false [.ident "OVERFLOWS"] none,
   .expr (.call (.ident "isNaN") [Square.sumSource "u"])]

theorem signals_rejected :
    Block.fromBlock Static.Bounded.integerCeiling (withDoStep [Square.overflowName] unsignaledBody) = none ∧
    Block.fromBlock Static.Bounded.integerCeiling (withDoStep [] (Square.checkedSource "u" "x" "J")) = none ∧
    Block.fromBlock Static.Bounded.integerCeiling (withDoStep [Square.overflowName] unraisedBody) = none ∧
    rejectedChecks.all (fun test =>
      (Block.fromBlock Static.Bounded.integerCeiling
        (withDoStep [Square.overflowName] (checkFormBody test))).isNone) = true := by
  decide +kernel

end Rumoca.EFMI.TensorAlgorithm
