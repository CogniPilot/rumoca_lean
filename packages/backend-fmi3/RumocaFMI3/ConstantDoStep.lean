import RumocaFMI3.TensorDoStep

/-! Constant-rate Co-Simulation `fmi3DoStep` body over the static constant-rate
instance record, as a package-checked product.

The constant-rate profile (`G01`) reuses the scalar unit-Euler grid policy: the
communication step must be a positive integer multiple of the internal unit step
and at most the scalar bound, otherwise `fmi3Discard` without advancing. The guard
prefix (handle/lifecycle guard, the output-pointer check and writes, the invalid
communication-point/step rejection, `stepRounding`, `stepClock`, `stepGrid`) is the
model-independent scalar prefix of `Runtime.doStep`, reused verbatim from the tensor
`fmi3DoStep`; only the numerical tail differs.

The numerical tail runs the outer grid loop over the admitted internal step count.
Each internal step advances the independent time base by one and calls the emitted
numerical entry `rumoca_constant_step(&(m->x[0]))`
(`packages/backend-c/RumocaC/ConstantKernelCode.lean`), which advances every state
by one explicit Euler step of its constant rate. The constant-rate profile's kernel
iterates the states internally, so the body needs no elementwise Euler loop and no
element count; over `N` accepted internal steps every state advances by the `N`-fold
finite rate sum and the time by `N`. After the loop the advanced time base is
published to `*lastSuccessfulTime` and the call returns `fmi3OK`.

The target semantics of the numerical entry are the constant-rate kernel contract
(`Rumoca.CConstant.contract_correct`): `rumoca_constant_step` is the finite
binary64 Euler update and its counted iteration is each state's independent
trajectory. The fused single-run observable execution of the numerical entry over
the instance record (the constant-rate analog of the tensor accepted-step
composition) is a later increment; this product proves the body's guard prefix,
printed text, closedness, denotation, null rejection and lifecycle rejection.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and the tensor and scalar adapters, `Runtime.lean` and
every existing contract are unchanged. -/
noncomputable section
namespace Rumoca.FMI3.ConstantDoStep
open CTree CMemory CBody CLoops
open Rumoca.FMI3.TensorInstance
open Rumoca.FMI3.TensorDoStep (signature signature_printable timeAdvance oneExpr stepPublishTail)

/-- The declaration-free constant internal-step body: call the numerical entry
`rumoca_constant_step(&(m->x[0]))`, which advances every state by one explicit
Euler step of its constant rate. Unlike the tensor internal step it needs no
derivative call and no elementwise Euler loop, so it introduces no declarations. -/
def stepBody : List Stmt := [.eval (Runtime.call "rumoca_constant_step" [Runtime.region stateName])]

/-- The time-augmented per-internal-step body: advance the time base by one, then
run the declaration-free constant state step. -/
def stepBodyT : List Stmt := timeAdvance ++ stepBody

theorem stepBodyT_noDecl : stepBodyT.all CLoops.noDeclarations = true := by
  simp [stepBodyT, stepBody, timeAdvance, Runtime.put, Runtime.field, Runtime.v, oneExpr,
    CAlgorithm.literal, Runtime.call, Runtime.region, CLoops.noDeclarations]

/-- The model-dependent numerical tail of the constant-rate `fmi3DoStep`: hoist the
internal step count and the loop counter to function scope, run the outer grid loop
(each time-augmented internal step advances the time base by one and calls
`rumoca_constant_step`), publish the advanced time and return `fmi3OK`. -/
def stepSolve : List Stmt :=
  .declare "size_t" "steps" (.cast "size_t" (Runtime.v "communicationStepSize")) ::
  .declare "size_t" "n" (Runtime.n 0) ::
  loop "n" (Runtime.v "steps") stepBodyT ::
  stepPublishTail

/-- The complete guarded constant-rate `fmi3DoStep` body: the model-independent
scalar guard prefix of `Runtime.doStep` (identical to the tensor body's prefix)
followed by the constant numerical tail. -/
def doStepBody : List Stmt :=
  Runtime.require .doStep ++
  [Runtime.pointerCheck ["eventHandlingNeeded", "terminateSimulation", "earlyReturn", "lastSuccessfulTime"],
   Runtime.out "eventHandlingNeeded" (Runtime.n 0), Runtime.out "terminateSimulation" (Runtime.n 0),
   Runtime.out "earlyReturn" (Runtime.n 0), Runtime.out "lastSuccessfulTime" (Runtime.field "time"),
   Runtime.reject (Runtime.any [Runtime.negate (Runtime.finite (Runtime.v "currentCommunicationPoint")),
     Runtime.negate (Runtime.finite (Runtime.v "communicationStepSize")),
     Runtime.nev (Runtime.v "currentCommunicationPoint") (Runtime.field "time"),
     Runtime.le (Runtime.v "communicationStepSize") (Runtime.n 0)])
     "Invalid communication point or step size"] ++
  Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ stepSolve

/-- The constant-rate `fmi3DoStep` function over the shared `fmi3DoStep` signature. -/
def function : CTree.Function := ⟨signature, doStepBody, false⟩

/-- The guard prefix of the constant body is exactly the model-independent scalar
prefix of `Runtime.doStep` (the 16 statements up to and including `stepGrid`); only
the trailing numerical section differs. -/
theorem doStepBody_prefix : doStepBody = Runtime.doStep.take 16 ++ stepSolve := rfl

theorem doStepBody_closed : doStepBody.all CBodyEmbedding.closedBlocks = true := by
  simp [doStepBody, stepSolve, stepBodyT, stepBody, timeAdvance, oneExpr, stepPublishTail,
    Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject, Runtime.branch,
    Runtime.pointerCheck, Runtime.out, Runtime.put, Runtime.stepRounding, Runtime.stepClock,
    Runtime.stepGrid, Runtime.stepDiscard, Runtime.log, Runtime.fail, Runtime.ret, Runtime.ok,
    Runtime.call, Runtime.region, Runtime.field, Runtime.v, Runtime.n, Runtime.any, Runtime.negate,
    Runtime.finite, Runtime.nev, Runtime.le, Runtime.both, Runtime.either, Runtime.put,
    CAlgorithm.literal, CBodyEmbedding.closedBlocks, CLoops.noDeclarations, CLoops.loop,
    CLoops.counterStep, List.all_append]

/-! ### Printed-text denotation -/

section
open CTree.Printer CTree.Syntax

set_option maxHeartbeats 8000000 in
theorem body_printable :
    ∀ stmt ∈ function.body, ItemPrintable RuntimePrinter.typedefs stmt := by
  have iType : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
    .pointer (text := "Instance") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have fType : TypeSpelling RuntimePrinter.typedefs "fmi3Float64 *" :=
    .pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have sType : TypeSpelling RuntimePrinter.typedefs "size_t" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  have intType : TypeSpelling RuntimePrinter.typedefs "int" := .named (.primitive (by decide +kernel))
  have doubleType : TypeSpelling RuntimePrinter.typedefs "double" := .named (.primitive (by decide +kernel))
  simp only [function, doStepBody, stepSolve, stepPublishTail, stepBodyT, stepBody, timeAdvance, oneExpr,
      Runtime.region, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression,
      permittedModes, Runtime.mode, Runtime.reject, Runtime.branch, Runtime.pointerCheck, Runtime.out,
      Runtime.put, Runtime.ok, Runtime.ret, Runtime.fail, Runtime.stepRounding, Runtime.stepClock,
      Runtime.stepGrid, Runtime.stepDiscard, Runtime.log, Runtime.field, Runtime.v, Runtime.n, Runtime.call,
      Runtime.any, Runtime.negate, Runtime.finite, Runtime.nev, Runtime.eqv, Runtime.le, Runtime.lt,
      Runtime.gt, Runtime.both, Runtime.either, CAlgorithm.literal, CLoops.loop, CLoops.counterStep,
      List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_imp, forall_and, List.cons_append, List.nil_append, forall_eq] <;>
    repeat first
      | exact CNull.literal_printable _
      | exact iType
      | exact fType
      | exact sType
      | exact intType
      | exact doubleType
      | apply And.intro
      | apply ItemPrintable.declare
      | apply ItemPrintable.assign
      | apply ItemPrintable.eval
      | apply ItemPrintable.branch
      | apply ItemPrintable.whileLoop
      | apply ItemPrintable.returnValue
      | apply Printable.cast
      | apply Printable.binary
      | apply Printable.not
      | apply Printable.dereference
      | apply Printable.address
      | apply Printable.call
      | apply Printable.field
      | apply Printable.index
      | exact Printable.natural
      | exact Printable.string
      | apply Printable.identifier
      | solve | intro stmt impossible; cases impossible
      | decide +kernel
      | simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
          Postfix, FieldBase]

/-- The rendered constant-rate `fmi3DoStep` denotes its function under the shared C
printer. -/
theorem function_denotes :
    FunctionDenotes RuntimePrinter.typedefs function.render function :=
  CTree.Printer.function_denotes ⟨signature_printable, body_printable⟩

end

/-! ### The pre-guard rejections

The handle and lifecycle guards are the model-independent scalar prefix, so a null
handle and a lifecycle-mismatched call are rejected exactly as the scalar and tensor
bodies reject them, reached before any numerical declaration. -/

section
variable [static : StaticLiterals]
private local instance rejectionInterface : CInterface := cInterface static.addresses
variable (program : CCalls.Events.Program E)

/-- A null instance handle is rejected with `fmi3Error`, changing nothing. -/
theorem null_behaviors (types : StepEntry.Types) (heap : Heap)
    (point step : BitVec 64) (flag : Bool) (outputs : StepEntry.Outputs)
    (defined : program.internal.definitions "fmi3DoStep" = some (.tree function)) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3DoStep" (StepEntry.arguments none point step flag outputs) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program function
    (Runtime.modeGuard .doStep :: (StepEntry.outputCode ++ StepEntry.inputGuard ::
      (Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ stepSolve)))
    (StepEntry.arguments none point step flag outputs) (StepEntry.parameters none point step flag outputs)
    heap defined (StepEntry.parameters_bound types none point step flag outputs)
    (by simp [function, doStepBody, Runtime.require, StepEntry.outputCode, StepEntry.inputGuard,
      StepEntry.inputCondition, List.append_assoc]) rfl doStepBody_closed
  all_goals simp [StepEntry.parameters, StepEntry.bindings, CBody.bind]

/-- A `fmi3DoStep` call in a disallowed FMI state is rejected with `fmi3Error`,
writing the terminated mode and (logging suppressed) changing nothing else. -/
theorem lifecycle_behaviors (types : StepEntry.Types) (heap : Heap)
    (p message : Address) (logger : Option Address) (kind : Kind) (mode : Mode)
    (point step : BitVec 64) (flag : Bool) (outputs : StepEntry.Outputs)
    (defined : program.internal.definitions "fmi3DoStep" = some (.tree function))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses ErrorCalls.rejectionMessage = some message)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0))
    (rejected : ¬ Reference.Allowed .doStep kind mode) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag outputs) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  apply GuardedCalls.rejected_silent_behaviors program function .doStep
    (StepEntry.outputCode ++ StepEntry.inputGuard ::
      (Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ stepSolve))
    (StepEntry.arguments (some p) point step flag outputs) (StepEntry.parameters (some p) point step flag outputs)
    heap p message logger kind mode defined (StepEntry.parameters_bound types (some p) point step flag outputs)
    (by simp [function, doStepBody, Runtime.require, StepEntry.outputCode, StepEntry.inputGuard,
      StepEntry.inputCondition, List.append_assoc]) rfl doStepBody_closed
    helper (by simp [StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [StepEntry.parameters, StepEntry.bindings, CBody.bind]) messageBound hk hm hl hg rejected

end

/-! ### Consumable function contract

This mirrors the pre-execution conjuncts of the tensor `fmi3DoStep` contract: the
printed function text, its declaration closedness, its printed-text denotation under
the shared C printer, and the null-handle rejection. The accepted end-to-end
execution over the constant-rate instance record and the off-grid `fmi3Discard` path
are companion obligations of a later increment. -/

section
open CTree.Printer
variable [static : StaticLiterals]
private local instance contractInterface : CInterface := cInterface static.addresses

/-- The constant-rate `fmi3DoStep` function contract (guard, print and null-rejection
conjuncts). -/
structure Contract (text : String) : Prop where
  printed : text = function.render
  closed : function.body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text function
  rejected : ∀ {E} (program : CCalls.Events.Program E) (types : StepEntry.Types) (heap : Heap)
    (point step : BitVec 64) (flag : Bool) (outputs : StepEntry.Outputs),
    program.internal.definitions "fmi3DoStep" = some (.tree function) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3DoStep" (StepEntry.arguments none point step flag outputs) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

theorem contract : Contract function.render where
  printed := rfl
  closed := doStepBody_closed
  denotes := function_denotes
  rejected program types heap point step flag outputs defined :=
    null_behaviors program types heap point step flag outputs defined

end

end Rumoca.FMI3.ConstantDoStep
