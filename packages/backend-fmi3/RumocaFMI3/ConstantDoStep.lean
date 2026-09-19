import RumocaFMI3.TensorDoStep
import RumocaFMI3.ConstantInstanceRhs

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
trajectory. The fused single-run observable execution composes the reused guard
prefix, the outer grid loop of `N` internal steps and the advanced-time publish into
one observable-machine execution: `accepted_behaviors`/`execution_free` prove the
accepted call's sole terminating behavior returns `fmi3OK` with the state region
advanced by the `N`-fold finite rate sum, the instance time cell and the caller's
`lastSuccessfulTime` reading the advanced time base, and every other instance
preserved. Alongside the accepted case this product proves the off-grid / over-bound
`fmi3Discard` path (`discard_suppressed_behaviors`/`discard_logged_behaviors`), the
body's guard prefix, printed text, closedness, denotation, null rejection and
lifecycle rejection.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and the tensor and scalar adapters, `Runtime.lean` and
every existing contract are unchanged. -/
noncomputable section
namespace Rumoca.FMI3.ConstantDoStep
open CTree CMemory CBody CLoops
open Rumoca.CMemory.TensorView
open Rumoca.FMI3.TensorInstance
open Rumoca.FMI3.TensorDoStep (signature signature_printable timeAdvance oneExpr stepPublishTail)
open Rumoca.ConstantProfile (Decimal)
open Rumoca.CConstant (rateVal)

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

/-! ### The header-aware constant floating-environment interface bundle

The constant-rate Co-Simulation step body reads the `FE_TONEAREST` rounding macro in
its guard prefix, so its proofs run in the floating-environment interface
`TensorDoStep.fenvInterface header`: the pinned C interface extended with the header's
round-to-nearest constant. `ConstantFenv` bundles the pinned type spellings and
helper/status constants the constant numerical tail resolves, together with the fact
that the emitted state-step entry `rumoca_constant_step` is not a bound constant (so it
resolves as a direct call). Both the pinned `cInterface` and the header-aware
floating-environment interface satisfy it; the `double *` header typing the numerical
entry needs is carried separately as `ptrTy`, exactly as the constant derivative getter
carries it. -/
structure ConstantFenv (interface : CInterface) : Prop where
  intType : interface.types "int" = some .int32
  doubleType : interface.types "double" = some .float64
  statusType : interface.types "fmi3Status" = some .int32
  sizeType : interface.types "size_t" = some .size
  fmi3OK : interface.constants "fmi3OK" = some (.integer 0)
  fegetround : interface.constants "fegetround" = none
  floorConstant : interface.constants "floor" = none
  constantStep : interface.constants "rumoca_constant_step" = none

/-- The pinned C interface supplies every pinned type spelling and helper/status
constant (`FE_TONEAREST` is carried separately when the guard runs). -/
theorem cInterface_fenv [static : StaticLiterals] : ConstantFenv (cInterface static.addresses) where
  intType := rfl
  doubleType := rfl
  statusType := rfl
  sizeType := rfl
  fmi3OK := rfl
  fegetround := rfl
  floorConstant := rfl
  constantStep := rfl

/-- The header-aware floating-environment interface supplies every pinned type
spelling and helper/status constant. -/
theorem fenvInterface_fenv [static : StaticLiterals] (header : CFenv.Header) :
    ConstantFenv (TensorDoStep.fenvInterface (static := static) header) where
  intType := rfl
  doubleType := rfl
  statusType := rfl
  sizeType := rfl
  fmi3OK := TensorDoStep.fenvInterface_constant header "fmi3OK" (by decide)
  fegetround := TensorDoStep.fenvInterface_constant header "fegetround" (by decide)
  floorConstant := TensorDoStep.fenvInterface_constant header "floor" (by decide)
  constantStep := TensorDoStep.fenvInterface_constant header "rumoca_constant_step" (by decide)

/-! ### One internal step over the constant instance record

The constant internal step advances the state by one explicit Euler step of its
constant rate: the emitted numerical entry `rumoca_constant_step(&(m->x[0]))` advances
every state cell by the finite binary64 addition of its rate
(`ConstantInstanceRhs.step_writes_events`), and the time base advances by one. Unlike
the tensor internal step it needs no derivative call and no elementwise Euler loop, so
the whole step is the time advance composed with one numerical-entry run. -/
section
variable [interface : CInterface]
variable (program : CCalls.Events.Program E)

/-- The entry-call step: from the running constant state-step body the observable
scheduler enters the constant-rate state step entry `rumoca_constant_step`, resolved
directly by name, with the instance's state region pointer `&(m->x[0])` as its only
argument and the remaining statements saved as the caller continuation. -/
theorem constant_step_enter (p : Address) (env : Locals) (types0 : Types) (H : Heap)
    (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (mBound : env "m" = some (.pointer (some p)))
    (freshStep : env "rumoca_constant_step" = none)
    (noConst : interface.constants "rumoca_constant_step" = none) :
    CCalls.Events.internalNext program
      (.body (.running (stepBody ++ rest) env types0 H) resultType stack) =
      some (.calling "rumoca_constant_step" [.pointer (some (p.member stateName))] H
        (.caller .discard rest env types0 resultType stack)) := by
  simp [stepBody, List.cons_append, List.nil_append, CCalls.Events.internalNext, CCalls.Typed.nextWith,
    CLoops.next, CLoops.eval, Runtime.call, Runtime.region, Runtime.field, Runtime.v, Runtime.n,
    CBody.eval, CBody.lvalue, CCalls.Events.enterCall, CCalls.Events.resolve, CCalls.Indirect.operand,
    CCalls.Indirect.resolve, CCalls.arguments, CBody.bind, CBody.resolve, CBody.constants, Value.address,
    mBound, freshStep, noConst]

/-- One constant Co-Simulation internal step from the time-augmented declaration-free
body `stepBodyT` over an arbitrary well-formed constant instance heap `H`: advance the
scalar time base by one, then advance the state region `x` by the finite binary64
addition of its constant rate through `rumoca_constant_step`. The reached heap's state
region reads `eulerVec rates state len`, its time cell reads the finite sum `t + 1`, and
every other cell of every other instance (and every cell outside the instance record)
is preserved. `finite`, `timeAdds` and `resolves` carry the per-cell finite addition,
the finite time addition and the direct helper resolution. -/
theorem internalStep_reaches {shape : Tensor.Shape} (rates : List Decimal) (len : rates.length = shape.volume)
    (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (found : definitions "rumoca_constant_step" = some (Rumoca.CConstant.stepFunction rates))
    (ptrTy : interface.types "double *" = some .pointer)
    (H : Heap) (pool : Address) (i : Nat)
    (state : Values shape) (t t' : Binary64.Value)
    (env : Locals) (types0 : Types) (resultType : String)
    (stack : CCalls.Typed.Continuation) (rest : List Stmt)
    (mBound : env "m" = some (.pointer (some (record pool i))))
    (freshStep : env "rumoca_constant_step" = none)
    (readsState : Reads H (field pool i stateName) state)
    (writableState : Writable H (field pool i stateName) shape.volume)
    (timeStored : H (field pool i timeName) = some ⟨.float64, true, some (.finite t)⟩)
    (finite : ∀ (k : Fin shape.volume),
      CExecution.finiteRoundDomain (Binary64.units state[k]
        + Binary64.units (rateVal (rates[k.val]'(ConstantInstanceRhs.idxLt len k)))))
    (timeAdds : Binary64.Adds t Binary64.one (.finite t'))
    (resolves : ∀ (Hn : Heap) (w), Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling "rumoca_constant_step" [.pointer (some (field pool i stateName))] Hn .done) w →
      CCalls.Events.Resolves program w) (fenv : ConstantFenv interface) :
    ∃ finalHeap,
      Reads finalHeap (field pool i stateName) (ConstantInstanceRhs.eulerVec rates state len) ∧
      Writable finalHeap (field pool i stateName) shape.volume ∧
      finalHeap (field pool i timeName) = some ⟨.float64, true, some (.finite t')⟩ ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((field pool j b).index k) = H ((field pool j b).index k)) ∧
      (∀ q, q.block ≠ (record pool i).block → finalHeap q = H q) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.body (.running (stepBodyT ++ rest) env types0 H) resultType stack)
        (.body (.running rest env types0 finalHeap) resultType stack) := by
  have tfield : field pool i timeName = (record pool i).member "time" := rfl
  set p := record pool i with hp
  set H1 := StateProofs.written H (p.member "time") (Binary64.toBits t').val with hH1
  have clockLoad : load H (p.member "time") = some (.finite t) := by
    rw [← tfield]; simp [load, timeStored, convert, Value.finite]
  have timeTrans : CLoops.next (.running (timeAdvance ++ (stepBody ++ rest)) env types0 H) =
      some (.running (stepBody ++ rest) env types0 H1) :=
    TensorDoStep.timeStep env types0 H p t t' (some (.finite t)) (stepBody ++ rest) fenv.doubleType
      mBound clockLoad (by rw [← tfield]; exact timeStored) timeAdds
  have time_ne : ∀ (nm : String) (a : Nat), nm ≠ timeName →
      (field pool i nm).index a ≠ p.member "time" := by
    intro nm a hnm
    rw [← tfield, show field pool i timeName = (field pool i timeName).index 0 from (Address.index_zero _).symm]
    exact fields_separate pool i nm timeName hnm a 0
  have frameH1 : ∀ (nm : String) (a : Nat), nm ≠ timeName →
      H1 ((field pool i nm).index a) = H ((field pool i nm).index a) :=
    fun nm a hnm => StateProofs.written_frame H (p.member "time") _ _ (time_ne nm a hnm)
  have readsStateH1 : Reads H1 (field pool i stateName) state := fun a => by
    simp only [load, frameH1 stateName a.val (by decide)]; exact readsState a
  have writableStateH1 : Writable H1 (field pool i stateName) shape.volume := fun a ha => by
    obtain ⟨old, ho⟩ := writableState a ha
    exact ⟨old, by rw [frameH1 stateName a (by decide)]; exact ho⟩
  set cont := CCalls.Typed.Continuation.caller .discard rest env types0 resultType stack with hcont
  have enterStep : CCalls.Events.internalNext program
      (.body (.running (stepBody ++ rest) env types0 H1) resultType stack) =
      some (.calling "rumoca_constant_step" [.pointer (some (p.member stateName))] H1 cont) :=
    constant_step_enter program p env types0 H1 rest resultType stack mBound freshStep fenv.constantStep
  obtain ⟨finalHeap, reads, writableStep, frame, others, ran⟩ :=
    ConstantInstanceRhs.step_writes_events (shape := shape) rates len definitions program linked found ptrTy
      H1 pool i state readsStateH1 writableStateH1 finite (resolves H1) cont
  have resumeStep : CCalls.Events.internalNext program (.returning .void finalHeap cont) =
      some (.body (.running rest env types0 finalHeap) resultType stack) := by
    simp [hcont, CCalls.Events.internalNext, CCalls.Typed.nextWith, CCalls.Typed.resume]
  refine ⟨finalHeap, reads, writableStep, ?_, ?_, ?_, ?_⟩
  · have neState : ∀ m, m < shape.volume → (field pool i timeName) ≠ (field pool i stateName).index m := by
      intro m _
      rw [show field pool i timeName = (field pool i timeName).index 0 from (Address.index_zero _).symm]
      exact fields_separate pool i timeName stateName (by decide) 0 m
    have frameTime := frame (field pool i timeName) neState
    have h1Time : H1 (field pool i timeName) = some ⟨.float64, true, some (.finite t')⟩ := by
      rw [tfield, hH1, StateProofs.written]; simp [replace, Value.finite]
    rw [frameTime, h1Time]
  · intro j b k different
    have frameOther := others j b k different
    have otherH1 : H1 ((field pool j b).index k) = H ((field pool j b).index k) := by
      apply StateProofs.written_frame
      rw [← tfield, show field pool i timeName = (field pool i timeName).index 0 from (Address.index_zero _).symm]
      exact Address.instances_separate pool j i different b timeName k 0
    rw [frameOther, otherH1]
  · intro q hq
    have qneState : ∀ m, m < shape.volume → q ≠ (field pool i stateName).index m := by
      intro m _ same
      exact hq ((congrArg Address.block same).trans (TensorDoStep.field_index_block pool i stateName m))
    have frameGen := frame q qneState
    have qneTime : q ≠ p.member "time" := by
      intro same
      have hb : (p.member "time").block = p.block := rfl
      exact hq ((congrArg Address.block same).trans hb)
    have h1frame : H1 q = H q := by
      rw [hH1]; exact StateProofs.written_frame H (p.member "time") q (Binary64.toBits t').val qneTime
    rw [frameGen, h1frame]
  · have assoc : stepBodyT ++ rest = timeAdvance ++ (stepBody ++ rest) := by
      simp [stepBodyT, List.append_assoc]
    rw [assoc]
    exact .next (CCalls.Events.body_step program timeTrans resultType stack)
      (.next enterStep (ran.trans (.next resumeStep (.refl _))))

end


/-! ### The N-step constant Co-Simulation grid loop

`stepLoop_reaches` iterates the time-augmented internal step `stepBodyT` `N` times
inside the outer counted loop `loop "n" steps stepBodyT`, by induction on the number of
completed steps. Because the constant step declares nothing and resets no inner
counter, the per-iteration local environment is exactly `counterEnv env0 "n" k`; no
inner-counter bookkeeping is needed. The state region advances by the `N`-fold finite
Euler step (`states k` with `states (k+1) = eulerVec rates (states k) len`), the scalar
time base advances by one unit per step to `times N`, and every cell of every other
instance (and every cell outside the instance record) is preserved. The per-step finite
additions are the premises `finite` (state) and `timeAdds` (time), and `resolves`
records the uniform direct resolution of the nested state-step call. -/
section
variable [interface : CInterface]
variable (program : CCalls.Events.Program E)

theorem stepLoop_reaches {shape : Tensor.Shape} (rates : List Decimal) (len : rates.length = shape.volume)
    (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (found : definitions "rumoca_constant_step" = some (Rumoca.CConstant.stepFunction rates))
    (ptrTy : interface.types "double *" = some .pointer)
    (H0 : Heap) (pool : Address) (i : Nat)
    (states : Nat → Values shape) (times : Nat → Binary64.Value) (N : Nat)
    (env0 : Locals) (types0 : Types) (resultType : String)
    (stack : CCalls.Typed.Continuation) (rest : List Stmt)
    (nBound : N < 2 ^ 64)
    (mBound : env0 "m" = some (.pointer (some (record pool i))))
    (typedN : types0 "n" = some .size)
    (stepsBound : CBody.resolve env0 "steps" = some (.integer N))
    (freshStep : env0 "rumoca_constant_step" = none)
    (readsState0 : Reads H0 (field pool i stateName) (states 0))
    (writableState0 : Writable H0 (field pool i stateName) shape.volume)
    (timeInit0 : H0 (field pool i timeName) = some ⟨.float64, true, some (.finite (times 0))⟩)
    (stateStep : ∀ n < N, states (n + 1) = ConstantInstanceRhs.eulerVec rates (states n) len)
    (finite : ∀ n < N, ∀ (k : Fin shape.volume),
      CExecution.finiteRoundDomain (Binary64.units (states n)[k]
        + Binary64.units (rateVal (rates[k.val]'(ConstantInstanceRhs.idxLt len k)))))
    (timeAdds : ∀ n < N, Binary64.Adds (times n) Binary64.one (.finite (times (n + 1))))
    (resolves : ∀ (Hn : Heap) (w), Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling "rumoca_constant_step" [.pointer (some (field pool i stateName))] Hn .done) w →
      CCalls.Events.Resolves program w) (fenv : ConstantFenv interface) :
    ∃ finalHeap,
      Reads finalHeap (field pool i stateName) (states N) ∧
      Writable finalHeap (field pool i stateName) shape.volume ∧
      finalHeap (field pool i timeName) = some ⟨.float64, true, some (.finite (times N))⟩ ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((field pool j b).index k) = H0 ((field pool j b).index k)) ∧
      (∀ q, q.block ≠ (record pool i).block → finalHeap q = H0 q) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.body (.running (loop "n" (Runtime.v "steps") stepBodyT :: rest)
          (counterEnv env0 "n" 0) types0 H0) resultType stack)
        (.body (.running rest (counterEnv env0 "n" N) types0 finalHeap) resultType stack) := by
  have stepsEval : ∀ (kk : Nat) (Hk : Heap),
      CBody.eval (counterEnv env0 "n" kk) Hk (Runtime.v "steps") = some (.integer N) := by
    intro kk Hk
    show CBody.resolve (counterEnv env0 "n" kk) "steps" = some (.integer N)
    rw [show CBody.resolve (counterEnv env0 "n" kk) "steps" = CBody.resolve env0 "steps" from by
      simp [counterEnv, CBody.resolve, CBody.bind]]
    exact stepsBound
  suffices key : ∀ k, k ≤ N → ∃ Hk,
      Reads Hk (field pool i stateName) (states k) ∧
      Writable Hk (field pool i stateName) shape.volume ∧
      Hk (field pool i timeName) = some ⟨.float64, true, some (.finite (times k))⟩ ∧
      (∀ (j : Nat) (b : String) (m : Nat), j ≠ i →
        Hk ((field pool j b).index m) = H0 ((field pool j b).index m)) ∧
      (∀ q, q.block ≠ (record pool i).block → Hk q = H0 q) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.body (.running (loop "n" (Runtime.v "steps") stepBodyT :: rest)
          (counterEnv env0 "n" 0) types0 H0) resultType stack)
        (.body (.running (loop "n" (Runtime.v "steps") stepBodyT :: rest)
          (counterEnv env0 "n" k) types0 Hk) resultType stack) by
    obtain ⟨HN, stateN, wStateN, timeN, othersN, genN, reachN⟩ := key N (le_refl N)
    have stop := CLoops.loop_stop (counterEnv env0 "n" N) types0 HN "n"
      (Runtime.v "steps") stepBodyT rest N (by simp [counterEnv, CBody.bind]) (stepsEval N HN) stepBodyT_noDecl
    exact ⟨HN, stateN, wStateN, timeN, othersN, genN,
      reachN.trans (.next (CCalls.Events.body_step program stop resultType stack) (.refl _))⟩
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨H0, readsState0, writableState0, timeInit0, fun _ _ _ _ => rfl, fun _ _ => rfl, .refl _⟩
  | succ k ih =>
    intro hk1
    have hk : k < N := Nat.lt_of_succ_le hk1
    obtain ⟨Hk, stateK, wStateK, timeK, othersK, genK, reachK⟩ := ih (le_of_lt hk)
    have enter := CLoops.loop_enter (counterEnv env0 "n" k) types0 Hk "n"
      (Runtime.v "steps") stepBodyT rest k N (by simp [counterEnv, CBody.bind]) (stepsEval k Hk) stepBodyT_noDecl hk
    obtain ⟨Dk, sumDk, wStateDk, timeDk, othersDk, genDk, stepReach⟩ :=
      internalStep_reaches program rates len definitions linked found ptrTy Hk pool i (states k)
        (times k) (times (k + 1)) (counterEnv env0 "n" k) types0 resultType stack
        (counterStep "n" :: loop "n" (Runtime.v "steps") stepBodyT :: rest)
        (by simp [counterEnv, CBody.bind, mBound]) (by simp [counterEnv, CBody.bind, freshStep])
        stateK wStateK timeK (finite k hk) (timeAdds k hk) resolves fenv
    have increment := CLoops.counter_step env0 types0 Dk "n" k
      (loop "n" (Runtime.v "steps") stepBodyT :: rest) typedN (by omega)
    refine ⟨Dk, ?_, wStateDk, timeDk, ?_, ?_, ?_⟩
    · rw [stateStep k hk]; exact sumDk
    · intro j b m different; rw [othersDk j b m different]; exact othersK j b m different
    · intro q hq; rw [genDk q hq]; exact genK q hq
    · refine reachK.trans (.next (CCalls.Events.body_step program enter resultType stack) ?_)
      refine stepReach.trans ?_
      exact .next (CCalls.Events.body_step program increment resultType stack) (.refl _)

/-! ### The model-dependent numerical tail as one observable execution

`solve_reaches` runs the constant numerical tail `stepSolve` from the post-guard state:
it declares the internal step count `steps` (the `size_t` cast of the admitted
communication step, so it equals the admitted count) and the loop counter `n`; runs the
outer grid loop `loop "n" steps stepBodyT` via `stepLoop_reaches` (advancing the state
region by the N-fold finite Euler step and the time base to the N-fold finite sum);
writes the advanced time base to `*lastSuccessfulTime`; and returns `fmi3OK`. The
reached heap's state region reads `states N`, its time cell and the caller's
`lastSuccessfulTime` both read `times N`, and every cell of every other instance is
preserved. -/
theorem solve_reaches {shape : Tensor.Shape} (rates : List Decimal) (len : rates.length = shape.volume)
    (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (found : definitions "rumoca_constant_step" = some (Rumoca.CConstant.stepFunction rates))
    (ptrTy : interface.types "double *" = some .pointer)
    (H : Heap) (pool : Address) (i : Nat)
    (states : Nat → Values shape) (times : Nat → Binary64.Value)
    (duration : CStatements.Counter) (step : Binary64.Value)
    (env : Locals) (types0 : Types) (stack : CCalls.Typed.Continuation)
    (buffers : StepEntry.Buffers) (oldLast : Option Value)
    (mBound : env "m" = some (.pointer (some (record pool i))))
    (stepValue : env "communicationStepSize" = some (.finite step))
    (stepCast : convert .size (.finite step) = some (.integer duration.val))
    (lastValue : env "lastSuccessfulTime" = some (.pointer (some buffers.last)))
    (freshSteps : env "steps" = none) (freshN : env "n" = none)
    (freshStep : env "rumoca_constant_step" = none) (freshOK : env "fmi3OK" = none)
    (readsState : Reads H (field pool i stateName) (states 0))
    (writableState : Writable H (field pool i stateName) shape.volume)
    (timeInit : H (field pool i timeName) = some ⟨.float64, true, some (.finite (times 0))⟩)
    (lastCell : H buffers.last = some ⟨.float64, true, oldLast⟩)
    (lastOutside : ∀ j : Nat, buffers.last.block ≠ (record pool j).block)
    (stateStep : ∀ n, states (n + 1) = ConstantInstanceRhs.eulerVec rates (states n) len)
    (finite : ∀ n, ∀ (k : Fin shape.volume),
      CExecution.finiteRoundDomain (Binary64.units (states n)[k]
        + Binary64.units (rateVal (rates[k.val]'(ConstantInstanceRhs.idxLt len k)))))
    (timeAdds : ∀ n, Binary64.Adds (times n) Binary64.one (.finite (times (n + 1))))
    (resolves : ∀ (Hn : Heap) (w), Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling "rumoca_constant_step" [.pointer (some (field pool i stateName))] Hn .done) w →
      CCalls.Events.Resolves program w) (fenv : ConstantFenv interface) :
    ∃ finalHeap,
      Reads finalHeap (field pool i stateName) (states duration.val) ∧
      finalHeap (field pool i timeName) = some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      finalHeap buffers.last = some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((field pool j b).index k) = H ((field pool j b).index k)) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.body (.running stepSolve env types0 H) "fmi3Status" stack)
        (.returning (.integer 0) finalHeap stack) := by
  set p := record pool i with hp
  -- The two hoisted declarations.
  set env1 := bind env "steps" (.integer duration.val) with henv1
  set types1 := bindType types0 "steps" .size with htypes1
  have stepEval : CLoops.eval env types0 H (.cast "size_t" (Runtime.v "communicationStepSize")) =
      some (.integer duration.val) := by
    have base : CBody.resolve env "communicationStepSize" = some (.finite step) := by
      simp [CBody.resolve, stepValue]
    simp [CLoops.eval, CBody.eval, base, CBody.expressionCast, Runtime.v, CBody.zeroLiteral,
      CBody.cast, stepCast, fenv.sizeType]
  have freshN1 : env1 "n" = none := by simp [henv1, CBody.bind, freshN]
  set env2 := counterEnv env1 "n" 0 with henv2
  set types2 := bindType types1 "n" .size with htypes2
  have declReach : Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running stepSolve env types0 H) "fmi3Status" stack)
      (.body (.running (loop "n" (Runtime.v "steps") stepBodyT :: stepPublishTail) env2 types2 H)
        "fmi3Status" stack) :=
    .next (CCalls.Events.body_step program
      (TensorFloat64.declare_step_e env types0 H "size_t" "steps"
        (.cast "size_t" (Runtime.v "communicationStepSize")) .size (.integer duration.val)
        (.integer duration.val) _ freshSteps fenv.sizeType stepEval
        (CLoops.convert_size_nat _ duration.isLt)) "fmi3Status" stack)
      (.next (CCalls.Events.body_step program
        (CLoops.counter_initialize env1 types1 H "n" _ freshN1 fenv.sizeType) "fmi3Status" stack)
        (.refl _))
  -- The loop entry environment carries every prepared binding.
  have mBound1 : env1 "m" = some (.pointer (some p)) := by
    simp [henv1, CBody.bind, mBound]
  have stepsBound1 : CBody.resolve env1 "steps" = some (.integer duration.val) := by
    simp [henv1, CBody.resolve, CBody.bind]
  have freshStep1 : env1 "rumoca_constant_step" = none := by
    simp [henv1, CBody.bind, freshStep]
  have typedN2 : types2 "n" = some .size := by simp [htypes2, CLoops.bindType]
  obtain ⟨loopHeap, stateN, wStateN, timeN, othersN, genN, loopReach⟩ :=
    stepLoop_reaches program rates len definitions linked found ptrTy H pool i states times duration.val
      env1 types2 "fmi3Status" stack stepPublishTail duration.isLt mBound1 typedN2 stepsBound1 freshStep1
      readsState writableState timeInit (fun n _ => stateStep n) (fun n _ => finite n) (fun n _ => timeAdds n)
      resolves fenv
  -- The publish/return tail.
  set tailEnv := counterEnv env1 "n" duration.val with htailEnv
  have mTail : tailEnv "m" = some (.pointer (some p)) := by
    simp [htailEnv, henv1, counterEnv, CBody.bind, mBound]
  have lastTail : CBody.resolve tailEnv "lastSuccessfulTime" = some (.pointer (some buffers.last)) := by
    simp [htailEnv, henv1, counterEnv, CBody.resolve, CBody.bind, lastValue]
  have okTail : tailEnv "fmi3OK" = none := by
    simp [htailEnv, henv2, henv1, counterEnv, CBody.bind, freshOK]
  have tfield : field pool i timeName = p.member "time" := rfl
  have timeMember : loopHeap (p.member "time") = some ⟨.float64, true, some (.finite (times duration.val))⟩ := by
    rw [← tfield]; exact timeN
  have timeLoad : load loopHeap (p.member "time") = some (.finite (times duration.val)) := by
    simp [load, timeMember, convert, Value.finite]
  have lastBlock : buffers.last.block ≠ (record pool i).block := lastOutside i
  have lastNe : buffers.last ≠ p.member "time" := by
    intro same
    have hb : (p.member "time").block = p.block := rfl
    exact lastBlock ((congrArg Address.block same).trans hb)
  have lastLoop : loopHeap buffers.last = some ⟨.float64, true, oldLast⟩ := by
    rw [genN buffers.last lastBlock]; exact lastCell
  set finalHeap := StateProofs.written loopHeap buffers.last (Binary64.toBits (times duration.val)).val with hfinal
  have outStep : CLoops.next (.running stepPublishTail tailEnv types2 loopHeap) =
      some (.running [Runtime.ok] tailEnv types2 finalHeap) := by
    have leftEval : CLoops.eval tailEnv types2 loopHeap (Runtime.field "time") =
        some (.finite (times duration.val)) := by
      show CBody.eval tailEnv loopHeap (Runtime.field "time") = some (.finite (times duration.val))
      have raw : CBody.eval tailEnv loopHeap (Runtime.field "time") = load loopHeap (p.member "time") := by
        simp [Runtime.field, Runtime.v, CBody.eval, CBody.resolve, mTail, Value.address]
      rw [raw]; exact timeLoad
    have addr : CBody.lvalue tailEnv loopHeap (.deref (Runtime.v "lastSuccessfulTime")) = some buffers.last := by
      simp [CBody.lvalue, Runtime.v, CBody.eval, lastTail, Value.address]
    simp [stepPublishTail, Runtime.out, Runtime.ok, CLoops.next, leftEval, addr, Value.finite,
      store_float64 loopHeap buffers.last oldLast _ lastLoop, hfinal, StateProofs.written]
  have okReach := TensorDoStep.finishOK program finalHeap tailEnv types2 stack okTail fenv.statusType fenv.fmi3OK
  refine ⟨finalHeap, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    have ne : (field pool i stateName).index a.val ≠ buffers.last :=
      (TensorDoStep.cell_block_ne pool i stateName a.val buffers.last lastBlock).symm
    have frame : finalHeap ((field pool i stateName).index a.val) = loopHeap ((field pool i stateName).index a.val) := by
      rw [hfinal]; exact StateProofs.written_frame loopHeap buffers.last _ _ ne
    simp only [load, frame]; exact stateN a
  · have frame : finalHeap (field pool i timeName) = loopHeap (field pool i timeName) := by
      rw [hfinal]
      exact StateProofs.written_frame loopHeap buffers.last (field pool i timeName)
        (Binary64.toBits (times duration.val)).val (fun h => lastNe (tfield ▸ h.symm))
    rw [frame]; exact timeN
  · rw [hfinal, StateProofs.written]; simp [replace, Value.finite]
  · intro j b k different
    have ne : (field pool j b).index k ≠ buffers.last :=
      (TensorDoStep.cell_block_ne pool j b k buffers.last (lastOutside j)).symm
    have frame : finalHeap ((field pool j b).index k) = loopHeap ((field pool j b).index k) := by
      rw [hfinal]; exact StateProofs.written_frame loopHeap buffers.last _ _ ne
    rw [frame]; exact othersN j b k different
  · exact declReach.trans
      (loopReach.trans (.next (CCalls.Events.body_step program outStep "fmi3Status" stack) okReach))

end


/-! ### The reused model-independent guard prefix

`front_run` runs the first nine statements of the constant `fmi3DoStep` body, which are
exactly the scalar prefix of `Runtime.doStep` (`doStepBody_prefix`): the
handle/lifecycle guard, the output-pointer check and the zero/last-time output writes,
and the invalid communication-point/step rejection. It reaches the
`stepRounding`/`stepClock`/`stepGrid` guard sections followed by the constant numerical
tail, with the record pointer bound and the output cells initialized. Because these
guard statements are model-independent, the scalar lemmas apply verbatim; only the
trailing numerical section is constant-rate specific. -/
section
variable [interface : CInterface]

theorem front_run (types : StepEntry.Types) (env : Locals) (heap : Heap)
    (p : Address) (buffers : StepEntry.Buffers) (point time step : Binary64.Value) (oldOutput : Option Value)
    (handle : env "instance" = some (.pointer (some p))) (fresh : env "m" = none)
    (kindValue : load heap (p.member "kind") = some (.integer 1))
    (modeValue : load heap (p.member "mode") = some (.integer 4))
    (pointValue : env "currentCommunicationPoint" = some (.finite point))
    (stepValue : env "communicationStepSize" = some (.finite step))
    (eventValue : env "eventHandlingNeeded" = some (.pointer (some buffers.event)))
    (terminateValue : env "terminateSimulation" = some (.pointer (some buffers.terminate)))
    (earlyValue : env "earlyReturn" = some (.pointer (some buffers.early)))
    (lastValue : env "lastSuccessfulTime" = some (.pointer (some buffers.last)))
    (clock : load heap (p.member "time") = some (.finite time))
    (same : Binary64.value point = Binary64.value time) (positive : 0 < Binary64.value step)
    (event : HistoryBodies.BoolWritable heap buffers.event)
    (terminate : HistoryBodies.BoolWritable heap buffers.terminate)
    (early : HistoryBodies.BoolWritable heap buffers.early)
    (last : heap buffers.last = some ⟨.float64, true, oldOutput⟩)
    (outsideEvent : buffers.event.block ≠ p.block) (outsideTerminate : buffers.terminate.block ≠ p.block)
    (outsideEarly : buffers.early.block ≠ p.block) (outsideLast : buffers.last.block ≠ p.block) :
    CBody.run 9 (.running doStepBody env heap) =
      some (.running (Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ stepSolve)
        (StepEntry.locals env p) (StepEntry.outputHeap heap buffers time)) := by
  set tail := Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ stepSolve with htail
  have entered := StepEntry.lifecycle_run types env heap p .cs .step
    (StepEntry.outputCode ++ StepEntry.inputGuard :: tail) handle fresh kindValue modeValue
  simp only [allowed, permittedModes] at entered
  have setup := StepEntry.outputs_run (StepEntry.locals env p) heap p buffers time oldOutput
    (StepEntry.inputGuard :: tail) (by simp [StepEntry.locals, CBody.bind])
    (by simpa [StepEntry.locals, CBody.bind] using eventValue)
    (by simpa [StepEntry.locals, CBody.bind] using terminateValue)
    (by simpa [StepEntry.locals, CBody.bind] using earlyValue)
    (by simpa [StepEntry.locals, CBody.bind] using lastValue) clock event terminate early last
    outsideEvent outsideTerminate outsideEarly
  have clockAfter : load (StepEntry.outputHeap heap buffers time) (p.member "time") = some (.finite time) := by
    simpa only [load, StepEntry.output_instance heap buffers time p (p.member "time")
      outsideEvent outsideTerminate outsideEarly outsideLast rfl] using clock
  have condition := StepEntry.input_condition (StepEntry.locals env p) (StepEntry.outputHeap heap buffers time) p
    point time step (by simp [StepEntry.locals, CBody.bind])
    (by simpa [StepEntry.locals, CBody.bind] using pointValue)
    (by simpa [StepEntry.locals, CBody.bind] using stepValue) clockAfter same positive
  have checked : CBody.run 1 (.running (StepEntry.inputGuard :: tail)
      (StepEntry.locals env p) (StepEntry.outputHeap heap buffers time)) =
      some (.running tail (StepEntry.locals env p) (StepEntry.outputHeap heap buffers time)) := by
    simp [CBody.run, CBody.next, StepEntry.inputGuard, Runtime.reject, Runtime.branch, condition,
      boolean, Value.truth]
  have decomp : doStepBody = Runtime.require .doStep ++ StepEntry.outputCode ++
      StepEntry.inputGuard :: tail := rfl
  have remaining : CBody.run 6 (.running (StepEntry.outputCode ++ StepEntry.inputGuard :: tail)
      (StepEntry.locals env p) heap) =
      some (.running tail (StepEntry.locals env p) (StepEntry.outputHeap heap buffers time)) := by
    rw [show (6:Nat) = 5 + 1 from rfl, CBody.run_add, setup]; exact checked
  rw [decomp, List.append_assoc, show (9:Nat) = 3 + 6 from rfl, CBody.run_add, entered]
  exact remaining

end

/-! ### The accepted constant `fmi3DoStep` call

`accepted_reaches`/`accepted_behaviors` compose the reused guard prefix (`front_run`,
then `StepGuards.rounding_path`/`clock_path`/`grid_path` under the admitted-duration
premises) with the constant numerical tail (`solve_reaches`). For a request that passes
the guard prefix over the constant instance record's metadata and time cells, the
observable machine's sole terminating behavior initializes the output cells, runs the
outer grid loop for the admitted step count, publishes the advanced time to
`*lastSuccessfulTime`, and returns `fmi3OK`; the state region equals the N-fold Euler
iterate, the instance time cell and the caller's `lastSuccessfulTime` read the advanced
time base, and every cell of every other instance is preserved. -/
section
open CTree.Printer StepGuards
variable [interface : CInterface]
variable (program : CCalls.Events.Program E)

set_option maxRecDepth 100000 in
theorem accepted_reaches {shape : Tensor.Shape} (rates : List Decimal) (len : rates.length = shape.volume)
    (types : StepEntry.Types) (header : CFenv.Header)
    (fenv : ConstantFenv interface) (nearest : interface.constants "FE_TONEAREST" = some (.integer header.nearest))
    (ptrTy : interface.types "double *" = some .pointer)
    (definitions : CLoops.Calls.Definitions) (linked : CCalls.Typed.Extends definitions program.internal)
    (found : definitions "rumoca_constant_step" = some (Rumoca.CConstant.stepFunction rates))
    (heap : Heap) (pool : Address) (i : Nat) (buffers : StepEntry.Buffers)
    (point step : Binary64.Value) (flag : Bool) (stop : Option Binary64.Value) (oldOutput : Option Value)
    (states : Nat → Values shape) (times : Nat → Binary64.Value)
    (rounding : program.externals "fegetround" = some (CMathCalls.roundingExternal fenv.intType header.nearest
      ⟨by have positive := header.nonnegative; omega, header.bounded⟩))
    (floorBound : program.externals "floor" = some (CMathCalls.floorExternal fenv.doubleType))
    (defined : program.internal.definitions "fmi3DoStep" = some (.tree function))
    (kindValue : load heap ((record pool i).member "kind") = some (.integer 1))
    (modeValue : load heap ((record pool i).member "mode") = some (.integer 4))
    (timeCell : heap ((record pool i).member "time") =
      some ⟨.float64, true, some (.finite (times 0))⟩)
    (same : Binary64.value point = Binary64.value (times 0))
    (enabled : load heap ((record pool i).member "stopDefined") = some (boolean stop.isSome))
    (limit : ∀ value, stop = some value →
      load heap ((record pool i).member "stop") = some (.finite value))
    (admitted : StepAdmission.AdmittedDuration step)
    (progress : Binary64.value (times 0) < Binary64.value (Binary64.roundedAdd (times 0) step))
    (withinStop : ∀ value, stop = some value →
      Binary64.value (Binary64.roundedAdd (times 0) step) ≤ Binary64.value value)
    (readsState : Reads heap (field pool i stateName) (states 0))
    (writableState : Writable heap (field pool i stateName) shape.volume)
    (event : HistoryBodies.BoolWritable heap buffers.event)
    (terminate : HistoryBodies.BoolWritable heap buffers.terminate)
    (early : HistoryBodies.BoolWritable heap buffers.early)
    (last : heap buffers.last = some ⟨.float64, true, oldOutput⟩)
    (outsideEvent : ∀ j : Nat, buffers.event.block ≠ (record pool j).block)
    (outsideTerminate : ∀ j : Nat, buffers.terminate.block ≠ (record pool j).block)
    (outsideEarly : ∀ j : Nat, buffers.early.block ≠ (record pool j).block)
    (outsideLast : ∀ j : Nat, buffers.last.block ≠ (record pool j).block)
    (stateStep : ∀ n, states (n + 1) = ConstantInstanceRhs.eulerVec rates (states n) len)
    (finite : ∀ n, ∀ (k : Fin shape.volume),
      CExecution.finiteRoundDomain (Binary64.units (states n)[k]
        + Binary64.units (rateVal (rates[k.val]'(ConstantInstanceRhs.idxLt len k)))))
    (timeAdds : ∀ n, Binary64.Adds (times n) Binary64.one (.finite (times (n + 1))))
    (resolves : ∀ (Hn : Heap) (w), Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling "rumoca_constant_step" [.pointer (some (field pool i stateName))] Hn .done) w →
      CCalls.Events.Resolves program w) :
    ∃ (duration : CStatements.Counter) (finalHeap : Heap),
      0 < duration.val ∧ duration.val ≤ 1000000 ∧ Binary64.value step = (duration.val : ℝ) ∧
      Reads finalHeap (field pool i stateName) (states duration.val) ∧
      finalHeap (field pool i timeName) =
        some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      finalHeap buffers.last = some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((field pool j b).index k) = heap ((field pool j b).index k)) ∧
      Transition.Events.Prefix (CCalls.Events.machine program)
        (.calling "fmi3DoStep" (StepEntry.arguments (some (record pool i))
          (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs) heap .done) []
        (.returning (.integer 0) finalHeap .done) := by
  set p := record pool i with hp
  set params := StepEntry.parameters (some p) (Binary64.toBits point).val (Binary64.toBits step).val flag
    buffers.outputs with hparams
  set after := StepEntry.outputHeap heap buffers (times 0) with hafter
  obtain ⟨duration, dpos, dbound, ddur, dcast⟩ := StepAdmission.duration_count step admitted
  have front9 := front_run types params heap p buffers point (times 0) step oldOutput
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind]) kindValue modeValue
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, Value.finite])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, Value.finite])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [load, timeCell, convert, Value.finite]) same admitted.1 event terminate early last
    (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i)
  obtain ⟨localTypes, entered⟩ := CCalls.Events.body_prefix_reaches program function
    (StepEntry.arguments (some p) (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs)
    params (StepEntry.locals params p) heap after
    (Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ stepSolve) .done 9
    defined (StepEntry.parameters_bound types _ _ _ _ _) doStepBody_closed front9
  have loaded (name : String) : load after (p.member name) = load heap (p.member name) := by
    simp only [load, hafter, StepEntry.output_instance heap buffers (times 0) p (p.member name)
      (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i) rfl]
  set later := StepEntry.locals params p with hlater
  have instanceValue : later "m" = some (.pointer (some p)) := by simp [hlater, StepEntry.locals, CBody.bind]
  have stepBound : later "communicationStepSize" = some (.finite step) := by
    simp [hlater, StepEntry.locals, hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, Value.finite]
  have fresh (name) (member : name ∈ ["rounding", "next", "floored", "fegetround", "floor",
      "FE_TONEAREST", "model_advance", "fmi3OK"]) : later name = none := by
    fin_cases member <;>
      simp [hlater, StepEntry.locals, hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind]
  let rounded := Binary64.roundedAdd (times 0) step
  let roundingEnv := CBody.bind later "rounding" (.integer header.nearest)
  let roundingTypes := CLoops.bindType localTypes "rounding" .int32
  let clockEnv := CBody.bind roundingEnv "next" (.finite rounded)
  let clockTypes := CLoops.bindType roundingTypes "next" .float64
  let gridEnv := CBody.bind clockEnv "floored" (.finite (Binary64.floorValue step))
  let gridTypes := CLoops.bindType clockTypes "floored" .float64
  have first := StepGuards.rounding_path program header later localTypes after header.nearest
    ⟨by have positive := header.nonnegative; omega, header.bounded⟩
    (Runtime.stepClock ++ Runtime.stepGrid ++ stepSolve) "fmi3Status" .done
    fenv.intType (fresh _ (by simp)) (fresh _ (by simp)) (fresh _ (by simp)) fenv.fegetround nearest rounding
  simp only at first
  have second := StepGuards.clock_path program roundingEnv roundingTypes after p (times 0) step stop
    (Runtime.stepGrid ++ stepSolve) "fmi3Status" .done fenv.doubleType
    (by simpa [roundingEnv, CBody.bind] using fresh "next" (by simp))
    (by simpa [roundingEnv, CBody.bind] using instanceValue)
    (by simpa [roundingEnv, CBody.bind] using stepBound) ((loaded "time").trans
      (by simp [load, timeCell, convert, Value.finite]))
    ((loaded "stopDefined").trans enabled) (fun v c => (loaded "stop").trans (limit v c))
  have noStop : ¬ StepGuards.AboveStop (.finite rounded) stop := by
    cases stop with
    | none => simp [StepGuards.AboveStop]
    | some v => exact not_lt.mpr (withinStop v rfl)
  have second' : Transition.Events.Prefix (CCalls.Events.machine program)
      (.body (.running (Runtime.stepClock ++ Runtime.stepGrid ++ stepSolve)
        roundingEnv roundingTypes after) "fmi3Status" .done) []
      (.body (.running (Runtime.stepGrid ++ stepSolve) clockEnv clockTypes after)
        "fmi3Status" .done) := by
    simpa [StepAdmission.duration_sum (times 0) step admitted, StepGuards.clockDestination, noStop,
      StepGuards.Progress, progress, rounded, clockEnv, clockTypes, Value.finite] using second
  have third := StepGuards.grid_path program clockEnv clockTypes after step stepSolve
    "fmi3Status" .done fenv.doubleType (by simpa [clockEnv, roundingEnv, CBody.bind] using fresh "floored" (by simp))
    (by simpa [clockEnv, roundingEnv, CBody.bind] using fresh "floor" (by simp)) fenv.floorConstant
    (by simpa [clockEnv, roundingEnv, CBody.bind] using stepBound) admitted.1 floorBound
  have third' : Transition.Events.Prefix (CCalls.Events.machine program)
      (.body (.running (Runtime.stepGrid ++ stepSolve) clockEnv clockTypes after) "fmi3Status" .done) []
      (.body (.running stepSolve gridEnv gridTypes after) "fmi3Status" .done) := by
    simpa [admitted, gridEnv, gridTypes] using third
  have frameCell : ∀ (nm : String) (a : Nat), after ((field pool i nm).index a) =
      heap ((field pool i nm).index a) := fun nm a =>
    StepEntry.output_instance heap buffers (times 0) p ((field pool i nm).index a)
      (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i) rfl
  have readsStateAfter : Reads after (field pool i stateName) (states 0) := fun a => by
    simp only [load, frameCell stateName a.val]; exact readsState a
  have writableStateAfter : Writable after (field pool i stateName) shape.volume :=
    fun a ha => by
      obtain ⟨old, ho⟩ := writableState a ha
      exact ⟨old, by rw [frameCell stateName a]; exact ho⟩
  have timeAfter : after (field pool i timeName) =
      some ⟨.float64, true, some (.finite (times 0))⟩ := by
    rw [show field pool i timeName = p.member "time" from rfl, hafter,
      StepEntry.output_instance heap buffers (times 0) p (p.member "time")
        (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i) rfl]; exact timeCell
  obtain ⟨_e, _t, _ea, lastAfter⟩ := StepEntry.output_values heap buffers (times 0) oldOutput event terminate early last
  obtain ⟨finalHeap, stateFinal, timeFinal, lastFinal, othersFinal, solveReach⟩ :=
    solve_reaches program rates len definitions linked found ptrTy after pool i states times duration step
      gridEnv gridTypes .done buffers (some (.finite (times 0)))
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, instanceValue, hp])
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, stepBound]) dcast
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters,
        StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters,
        StepEntry.bindings, CBody.bind]) (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals,
        hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind]) (by simp [gridEnv, clockEnv, roundingEnv,
        CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind])
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters,
        StepEntry.bindings, CBody.bind]) readsStateAfter writableStateAfter timeAfter lastAfter outsideLast
      stateStep finite timeAdds resolves fenv
  refine ⟨duration, finalHeap, dpos, dbound, ddur, stateFinal, timeFinal, lastFinal, ?_, ?_⟩
  · intro j b k different
    have frameAfter : after ((field pool j b).index k) = heap ((field pool j b).index k) :=
      StepEntry.output_instance heap buffers (times 0) p ((field pool j b).index k)
        (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i) rfl
    rw [othersFinal j b k different, frameAfter]
  · refine (CCalls.Events.internal_path program entered).trans (first.trans (second'.trans (third'.trans ?_)))
    exact CCalls.Events.internal_path program solveReach

set_option maxRecDepth 100000 in
theorem accepted_behaviors {shape : Tensor.Shape} (rates : List Decimal) (len : rates.length = shape.volume)
    (types : StepEntry.Types) (header : CFenv.Header)
    (fenv : ConstantFenv interface) (nearest : interface.constants "FE_TONEAREST" = some (.integer header.nearest))
    (ptrTy : interface.types "double *" = some .pointer)
    (definitions : CLoops.Calls.Definitions) (linked : CCalls.Typed.Extends definitions program.internal)
    (found : definitions "rumoca_constant_step" = some (Rumoca.CConstant.stepFunction rates))
    (heap : Heap) (pool : Address) (i : Nat) (buffers : StepEntry.Buffers)
    (point step : Binary64.Value) (flag : Bool) (stop : Option Binary64.Value) (oldOutput : Option Value)
    (states : Nat → Values shape) (times : Nat → Binary64.Value)
    (rounding : program.externals "fegetround" = some (CMathCalls.roundingExternal fenv.intType header.nearest
      ⟨by have positive := header.nonnegative; omega, header.bounded⟩))
    (floorBound : program.externals "floor" = some (CMathCalls.floorExternal fenv.doubleType))
    (defined : program.internal.definitions "fmi3DoStep" = some (.tree function))
    (kindValue : load heap ((record pool i).member "kind") = some (.integer 1))
    (modeValue : load heap ((record pool i).member "mode") = some (.integer 4))
    (timeCell : heap ((record pool i).member "time") =
      some ⟨.float64, true, some (.finite (times 0))⟩)
    (same : Binary64.value point = Binary64.value (times 0))
    (enabled : load heap ((record pool i).member "stopDefined") = some (boolean stop.isSome))
    (limit : ∀ value, stop = some value →
      load heap ((record pool i).member "stop") = some (.finite value))
    (admitted : StepAdmission.AdmittedDuration step)
    (progress : Binary64.value (times 0) < Binary64.value (Binary64.roundedAdd (times 0) step))
    (withinStop : ∀ value, stop = some value →
      Binary64.value (Binary64.roundedAdd (times 0) step) ≤ Binary64.value value)
    (readsState : Reads heap (field pool i stateName) (states 0))
    (writableState : Writable heap (field pool i stateName) shape.volume)
    (event : HistoryBodies.BoolWritable heap buffers.event)
    (terminate : HistoryBodies.BoolWritable heap buffers.terminate)
    (early : HistoryBodies.BoolWritable heap buffers.early)
    (last : heap buffers.last = some ⟨.float64, true, oldOutput⟩)
    (outsideEvent : ∀ j : Nat, buffers.event.block ≠ (record pool j).block)
    (outsideTerminate : ∀ j : Nat, buffers.terminate.block ≠ (record pool j).block)
    (outsideEarly : ∀ j : Nat, buffers.early.block ≠ (record pool j).block)
    (outsideLast : ∀ j : Nat, buffers.last.block ≠ (record pool j).block)
    (stateStep : ∀ n, states (n + 1) = ConstantInstanceRhs.eulerVec rates (states n) len)
    (finite : ∀ n, ∀ (k : Fin shape.volume),
      CExecution.finiteRoundDomain (Binary64.units (states n)[k]
        + Binary64.units (rateVal (rates[k.val]'(ConstantInstanceRhs.idxLt len k)))))
    (timeAdds : ∀ n, Binary64.Adds (times n) Binary64.one (.finite (times (n + 1))))
    (resolves : ∀ (Hn : Heap) (w), Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling "rumoca_constant_step" [.pointer (some (field pool i stateName))] Hn .done) w →
      CCalls.Events.Resolves program w) :
    ∃ (duration : CStatements.Counter) (finalHeap : Heap),
      0 < duration.val ∧ duration.val ≤ 1000000 ∧ Binary64.value step = (duration.val : ℝ) ∧
      Reads finalHeap (field pool i stateName) (states duration.val) ∧
      finalHeap (field pool i timeName) =
        some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      finalHeap buffers.last = some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((field pool j b).index k) = heap ((field pool j b).index k)) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some (record pool i))
          (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, finalHeap⟩ := by
  obtain ⟨duration, finalHeap, dpos, dbound, ddur, stateFinal, timeFinal, lastFinal, othersFinal, reach⟩ :=
    accepted_reaches program rates len types header fenv nearest ptrTy definitions linked found heap pool i buffers
      point step flag stop oldOutput states times rounding floorBound defined kindValue modeValue timeCell same
      enabled limit admitted progress withinStop readsState writableState event terminate early last outsideEvent
      outsideTerminate outsideEarly outsideLast stateStep finite timeAdds resolves
  exact ⟨duration, finalHeap, dpos, dbound, ddur, stateFinal, timeFinal, lastFinal, othersFinal,
    fun behavior => (reach.forced (CCalls.Events.return_forced program (.integer 0) finalHeap)).behaviors behavior⟩

end


/-! ### The accepted end-to-end constant execution

`ExecutionFree` is the accepted end-to-end behavior of the constant `fmi3DoStep`: it
advances the state by the admitted number of unit Euler steps (each state cell by the
finite binary64 addition of its constant rate) and publishes the advanced time,
preserving every other instance. The C floating-environment interface is the
header-aware constant interface, so the round-to-nearest guard and `fmi3OK` return
resolve; the `double *` header-typing premise records the interface obligation the
numerical entry needs, carried like the constant derivative getter's, and the only
remaining external premise is the modeled `fegetround`/`floor` platform returns. -/
section
open CTree.Printer
variable [static : StaticLiterals]

def ExecutionFree (header : CFenv.Header) : Prop :=
    letI : CInterface := TensorDoStep.fenvInterface header
    ∀ {E} (program : CCalls.Events.Program E) (ptypes : StepEntry.Types) {shape : Tensor.Shape}
    (rates : List Decimal) (len : rates.length = shape.volume)
    (definitions : CLoops.Calls.Definitions) (linked : CCalls.Typed.Extends definitions program.internal)
    (found : definitions "rumoca_constant_step" = some (Rumoca.CConstant.stepFunction rates))
    (ptrTy : (TensorDoStep.fenvInterface header).types "double *" = some .pointer)
    (heap : Heap) (pool : Address) (i : Nat) (buffers : StepEntry.Buffers)
    (point step : Binary64.Value) (flag : Bool) (stop : Option Binary64.Value) (oldOutput : Option Value)
    (states : Nat → Values shape) (times : Nat → Binary64.Value),
    program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest
      ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
    program.externals "floor" = some (CMathCalls.floorExternal rfl) →
    program.internal.definitions "fmi3DoStep" = some (.tree function) →
    load heap ((record pool i).member "kind") = some (.integer 1) →
    load heap ((record pool i).member "mode") = some (.integer 4) →
    heap ((record pool i).member "time") =
      some ⟨.float64, true, some (.finite (times 0))⟩ →
    Binary64.value point = Binary64.value (times 0) →
    load heap ((record pool i).member "stopDefined") = some (boolean stop.isSome) →
    (∀ value, stop = some value →
      load heap ((record pool i).member "stop") = some (.finite value)) →
    StepAdmission.AdmittedDuration step →
    Binary64.value (times 0) < Binary64.value (Binary64.roundedAdd (times 0) step) →
    (∀ value, stop = some value →
      Binary64.value (Binary64.roundedAdd (times 0) step) ≤ Binary64.value value) →
    Reads heap (field pool i stateName) (states 0) →
    Writable heap (field pool i stateName) shape.volume →
    HistoryBodies.BoolWritable heap buffers.event → HistoryBodies.BoolWritable heap buffers.terminate →
    HistoryBodies.BoolWritable heap buffers.early → heap buffers.last = some ⟨.float64, true, oldOutput⟩ →
    (∀ j : Nat, buffers.event.block ≠ (record pool j).block) →
    (∀ j : Nat, buffers.terminate.block ≠ (record pool j).block) →
    (∀ j : Nat, buffers.early.block ≠ (record pool j).block) →
    (∀ j : Nat, buffers.last.block ≠ (record pool j).block) →
    (∀ n, states (n + 1) = ConstantInstanceRhs.eulerVec rates (states n) len) →
    (∀ n, ∀ (k : Fin shape.volume),
      CExecution.finiteRoundDomain (Binary64.units (states n)[k]
        + Binary64.units (rateVal (rates[k.val]'(ConstantInstanceRhs.idxLt len k))))) →
    (∀ n, Binary64.Adds (times n) Binary64.one (.finite (times (n + 1)))) →
    (∀ (Hn : Heap) (w), Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling "rumoca_constant_step" [.pointer (some (field pool i stateName))] Hn .done) w →
      CCalls.Events.Resolves program w) →
    ∃ (duration : CStatements.Counter) (finalHeap : Heap),
      0 < duration.val ∧ duration.val ≤ 1000000 ∧ Binary64.value step = (duration.val : ℝ) ∧
      Reads finalHeap (field pool i stateName) (states duration.val) ∧
      finalHeap (field pool i timeName) =
        some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      finalHeap buffers.last = some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((field pool j b).index k) = heap ((field pool j b).index k)) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some (record pool i))
          (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, finalHeap⟩

theorem execution_free (header : CFenv.Header) : ExecutionFree header := by
  letI : CInterface := TensorDoStep.fenvInterface header
  intro E program ptypes shape rates len definitions linked found ptrTy heap pool i buffers point step flag stop
      oldOutput states times rounding floorBound defined kindValue modeValue timeCell same enabled limit admitted
      progress withinStop readsState writableState event terminate early last outsideEvent outsideTerminate
      outsideEarly outsideLast stateStep finite timeAdds resolves
  exact accepted_behaviors program rates len ptypes header (fenvInterface_fenv header)
      (TensorDoStep.fenvInterface_nearest header) ptrTy definitions linked found heap pool i buffers point step flag stop
      oldOutput states times rounding floorBound defined kindValue modeValue timeCell same enabled limit admitted
      progress withinStop readsState writableState event terminate early last outsideEvent outsideTerminate
      outsideEarly outsideLast stateStep finite timeAdds resolves

end


section
open CTree.Printer StepGuards
open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile Rumoca.CTensor
variable [static : StaticLiterals]

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- The reused guard prefix over the tensor instance heap reaches the shared
`Runtime.stepDiscard` block for an off-grid or over-bound admitted step. -/
theorem discard_prefix
    (header : CFenv.Header) :
    letI : CInterface := TensorDoStep.fenvInterface (static := static) header
    ∀ {E} (program : CCalls.Events.Program E) (types : StepEntry.Types) (heap : Heap) (pool : Address) (i : Nat)
      (buffers : StepEntry.Buffers) (point step time : Binary64.Value) (flag : Bool)
      (stop : Option Binary64.Value) (oldOutput : Option Value),
      program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      program.externals "floor" = some (CMathCalls.floorExternal rfl) →
      program.internal.definitions "fmi3DoStep" = some (.tree (function)) →
      load heap ((TensorInstance.record pool i).member "kind") = some (.integer 1) →
      load heap ((TensorInstance.record pool i).member "mode") = some (.integer 4) →
      heap ((TensorInstance.record pool i).member "time") = some ⟨.float64, true, some (.finite time)⟩ →
      Binary64.value point = Binary64.value time →
      load heap ((TensorInstance.record pool i).member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value →
        load heap ((TensorInstance.record pool i).member "stop") = some (.finite value)) →
      HistoryBodies.BoolWritable heap buffers.event → HistoryBodies.BoolWritable heap buffers.terminate →
      HistoryBodies.BoolWritable heap buffers.early → heap buffers.last = some ⟨.float64, true, oldOutput⟩ →
      (∀ j : Nat, buffers.event.block ≠ (TensorInstance.record pool j).block) →
      (∀ j : Nat, buffers.terminate.block ≠ (TensorInstance.record pool j).block) →
      (∀ j : Nat, buffers.early.block ≠ (TensorInstance.record pool j).block) →
      (∀ j : Nat, buffers.last.block ≠ (TensorInstance.record pool j).block) →
      0 < Binary64.value step →
      StepGuards.Progress time (Binary64.addResult time step) →
      ¬ StepGuards.AboveStop (Binary64.addResult time step) stop →
      ¬ StepAdmission.AdmittedDuration step →
      StepDiscard.Path program
        (.calling "fmi3DoStep" (StepEntry.arguments (some (TensorInstance.record pool i))
          (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs) heap .done)
        (StepEntry.outputHeap heap buffers time) (TensorInstance.record pool i) := by
  letI : CInterface := TensorDoStep.fenvInterface header
  have fenv : ConstantFenv (TensorDoStep.fenvInterface header) := fenvInterface_fenv header
  have nearest : (TensorDoStep.fenvInterface (static := static) header).constants "FE_TONEAREST" =
    some (.integer header.nearest) := TensorDoStep.fenvInterface_nearest header
  intro E program types heap pool i buffers point step time flag stop oldOutput rounding floorBound defined
    kindValue modeValue timeCell same enabled limit event terminate early last outsideEvent outsideTerminate
    outsideEarly outsideLast positive progress noStop offGrid
  set p := TensorInstance.record pool i with hp
  set params := StepEntry.parameters (some p) (Binary64.toBits point).val (Binary64.toBits step).val flag
    buffers.outputs with hparams
  set after := StepEntry.outputHeap heap buffers time with hafter
  have front9 := front_run types params heap p buffers point time step oldOutput
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind]) kindValue modeValue
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, Value.finite])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, Value.finite])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [load, timeCell, convert, Value.finite]) same positive event terminate early last
    (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i)
  obtain ⟨localTypes, entered⟩ := CCalls.Events.body_prefix_reaches program (function)
    (StepEntry.arguments (some p) (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs)
    params (StepEntry.locals params p) heap after
    (Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ stepSolve) .done 9
    defined (StepEntry.parameters_bound types _ _ _ _ _) (doStepBody_closed) front9
  have loaded (name : String) : load after (p.member name) = load heap (p.member name) := by
    simp only [load, hafter, StepEntry.output_instance heap buffers time p (p.member name)
      (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i) rfl]
  set later := StepEntry.locals params p with hlater
  have instanceValue : later "m" = some (.pointer (some p)) := by simp [hlater, StepEntry.locals, CBody.bind]
  have stepBound : later "communicationStepSize" = some (.finite step) := by
    simp [hlater, StepEntry.locals, hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, Value.finite]
  have fresh (name) (member : name ∈ ["rounding", "next", "floored", "fegetround", "floor",
      "FE_TONEAREST", "model_advance", "fmi3OK"]) : later name = none := by
    fin_cases member <;>
      simp [hlater, StepEntry.locals, hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind]
  let candidate := Binary64.addResult time step
  let roundingEnv := CBody.bind later "rounding" (.integer header.nearest)
  let roundingTypes := CLoops.bindType localTypes "rounding" .int32
  let clockEnv := CBody.bind roundingEnv "next" (.float64 candidate.encode)
  let clockTypes := CLoops.bindType roundingTypes "next" .float64
  let gridEnv := CBody.bind clockEnv "floored" (.finite (Binary64.floorValue step))
  let gridTypes := CLoops.bindType clockTypes "floored" .float64
  have first := StepGuards.rounding_path program header later localTypes after header.nearest
    ⟨by have positive := header.nonnegative; omega, header.bounded⟩
    (Runtime.stepClock ++ Runtime.stepGrid ++ stepSolve) "fmi3Status" .done
    fenv.intType (fresh _ (by simp)) (fresh _ (by simp)) (fresh _ (by simp)) fenv.fegetround nearest rounding
  simp only at first
  have second := StepGuards.clock_path program roundingEnv roundingTypes after p time step stop
    (Runtime.stepGrid ++ stepSolve) "fmi3Status" .done fenv.doubleType
    (by simpa [roundingEnv, CBody.bind] using fresh "next" (by simp))
    (by simpa [roundingEnv, CBody.bind] using instanceValue)
    (by simpa [roundingEnv, CBody.bind] using stepBound) ((loaded "time").trans
      (by simp [load, timeCell, convert, Value.finite]))
    ((loaded "stopDefined").trans enabled) (fun v c => (loaded "stop").trans (limit v c))
  have second' : Transition.Events.Prefix (CCalls.Events.machine program)
      (.body (.running (Runtime.stepClock ++ Runtime.stepGrid ++ stepSolve)
        roundingEnv roundingTypes after) "fmi3Status" .done) []
      (.body (.running (Runtime.stepGrid ++ stepSolve) clockEnv clockTypes after)
        "fmi3Status" .done) := by
    simpa only [StepGuards.clockDestination, noStop, progress, ↓reduceIte, List.nil_append,
      clockEnv, clockTypes, candidate] using second
  have third := StepGuards.grid_path program clockEnv clockTypes after step (stepSolve)
    "fmi3Status" .done fenv.doubleType (by simpa [clockEnv, roundingEnv, CBody.bind] using fresh "floored" (by simp))
    (by simpa [clockEnv, roundingEnv, CBody.bind] using fresh "floor" (by simp)) fenv.floorConstant
    (by simpa [clockEnv, roundingEnv, CBody.bind] using stepBound) positive floorBound
  have third' : Transition.Events.Prefix (CCalls.Events.machine program)
      (.body (.running (Runtime.stepGrid ++ stepSolve) clockEnv clockTypes after) "fmi3Status" .done) []
      (.body (.running (Runtime.stepDiscard ++ stepSolve) gridEnv gridTypes after) "fmi3Status" .done) := by
    simpa [offGrid, gridEnv, gridTypes] using third
  refine ⟨gridEnv, gridTypes, stepSolve,
    (CCalls.Events.internal_path program entered).trans (first.trans (second'.trans third')), ?_, ?_⟩
  · simp [gridEnv, clockEnv, roundingEnv, CBody.bind, CBody.resolve, hlater, StepEntry.locals, hparams,
      StepEntry.parameters, StepEntry.bindings, hp]
  · simp [gridEnv, clockEnv, roundingEnv, CBody.bind, CBody.resolve, hlater, StepEntry.locals, hparams,
      StepEntry.parameters, StepEntry.bindings, CBody.constants,
      TensorDoStep.fenvInterface_constant header "fmi3Discard" (by decide)]

/-- With logging suppressed, an off-grid or over-bound admitted step returns
`fmi3Discard`, leaving the heap unchanged apart from the scalar output-cell
initialization. -/
def DiscardSuppressed (header : CFenv.Header) : Prop :=
    letI : CInterface := TensorDoStep.fenvInterface (static := static) header
    ∀ {E} (program : CCalls.Events.Program E) (types : StepEntry.Types) (heap : Heap) (pool : Address) (i : Nat)
      (buffers : StepEntry.Buffers) (point step time : Binary64.Value) (flag : Bool)
      (stop : Option Binary64.Value) (oldOutput : Option Value) (logger : Option Address) (logging : Bool),
      program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      program.externals "floor" = some (CMathCalls.floorExternal rfl) →
      program.internal.definitions "fmi3DoStep" = some (.tree (function)) →
      load heap ((TensorInstance.record pool i).member "kind") = some (.integer 1) →
      load heap ((TensorInstance.record pool i).member "mode") = some (.integer 4) →
      heap ((TensorInstance.record pool i).member "time") = some ⟨.float64, true, some (.finite time)⟩ →
      Binary64.value point = Binary64.value time →
      load heap ((TensorInstance.record pool i).member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value →
        load heap ((TensorInstance.record pool i).member "stop") = some (.finite value)) →
      HistoryBodies.BoolWritable heap buffers.event → HistoryBodies.BoolWritable heap buffers.terminate →
      HistoryBodies.BoolWritable heap buffers.early → heap buffers.last = some ⟨.float64, true, oldOutput⟩ →
      (∀ j : Nat, buffers.event.block ≠ (TensorInstance.record pool j).block) →
      (∀ j : Nat, buffers.terminate.block ≠ (TensorInstance.record pool j).block) →
      (∀ j : Nat, buffers.early.block ≠ (TensorInstance.record pool j).block) →
      (∀ j : Nat, buffers.last.block ≠ (TensorInstance.record pool j).block) →
      0 < Binary64.value step →
      StepGuards.Progress time (Binary64.addResult time step) →
      ¬ StepGuards.AboveStop (Binary64.addResult time step) stop →
      ¬ StepAdmission.AdmittedDuration step →
      load heap ((TensorInstance.record pool i).member "logger") = some (.pointer logger) →
      load heap ((TensorInstance.record pool i).member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) → ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some (TensorInstance.record pool i))
          (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 2, StepEntry.outputHeap heap buffers time⟩

set_option maxRecDepth 100000 in
theorem discard_suppressed_behaviors (header : CFenv.Header) :
    DiscardSuppressed header := by
  letI : CInterface := TensorDoStep.fenvInterface (static := static) header
  intro E program types heap pool i buffers point step time flag stop oldOutput logger logging rounding floorBound
    defined kindValue modeValue timeCell same enabled limit event terminate early last outsideEvent outsideTerminate
    outsideEarly outsideLast positive progress noStop offGrid loggerValue loggingValue suppressed behavior
  set p := TensorInstance.record pool i with hp
  have loaded (name : String) :
      load (StepEntry.outputHeap heap buffers time) (p.member name) = load heap (p.member name) := by
    simp only [load, StepEntry.output_instance heap buffers time p (p.member name)
      (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i) rfl]
  obtain ⟨env, gtypes, rest, reached, instanceValue, statusValue⟩ :=
    discard_prefix header program types heap pool i buffers point step time flag stop oldOutput
      rounding floorBound defined kindValue modeValue timeCell same enabled limit event terminate early last
      outsideEvent outsideTerminate outsideEarly outsideLast positive progress noStop offGrid
  have result := StepDiscard.suppressed_behaviors (TensorDoStep.fenvErrorContext header) program env gtypes rest
    (StepEntry.outputHeap heap buffers time) p logger logging instanceValue statusValue
    ((loaded "logger").trans loggerValue) ((loaded "logging").trans loggingValue) suppressed
  exact (reached.silent_finite_behaviors (by intro history divergent; have impossible := (result (.diverges history)).mp divergent; simp at impossible) behavior).trans (result behavior)

/-- With logging enabled, an off-grid or over-bound admitted step returns
`fmi3Discard` after invoking the logging callback, mirroring every represented
callback outcome; the heap is unchanged apart from the scalar output-cell
initialization and the callback's own writes. -/
def DiscardLogged (header : CFenv.Header) : Prop :=
    letI : CInterface := TensorDoStep.fenvInterface (static := static) header
    ∀ {E} (program : CCalls.Events.Program E) (types : StepEntry.Types) (heap : Heap) (pool : Address) (i : Nat)
      (buffers : StepEntry.Buffers) (point step time : Binary64.Value) (flag : Bool)
      (stop : Option Binary64.Value) (oldOutput : Option Value)
      (text category logger : Address) (environment : Option Address) (name : String)
      (foreign : CCalls.Events.External E),
      program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      program.externals "floor" = some (CMathCalls.floorExternal rfl) →
      program.internal.definitions "fmi3DoStep" = some (.tree (function)) →
      static.addresses "logStatus" = some category → static.addresses StepDiscard.message = some text →
      program.addresses logger = some name → program.externals name = some foreign →
      foreign.signature = Logging.signature name →
      load heap ((TensorInstance.record pool i).member "kind") = some (.integer 1) →
      load heap ((TensorInstance.record pool i).member "mode") = some (.integer 4) →
      heap ((TensorInstance.record pool i).member "time") = some ⟨.float64, true, some (.finite time)⟩ →
      Binary64.value point = Binary64.value time →
      load heap ((TensorInstance.record pool i).member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value →
        load heap ((TensorInstance.record pool i).member "stop") = some (.finite value)) →
      HistoryBodies.BoolWritable heap buffers.event → HistoryBodies.BoolWritable heap buffers.terminate →
      HistoryBodies.BoolWritable heap buffers.early → heap buffers.last = some ⟨.float64, true, oldOutput⟩ →
      (∀ j : Nat, buffers.event.block ≠ (TensorInstance.record pool j).block) →
      (∀ j : Nat, buffers.terminate.block ≠ (TensorInstance.record pool j).block) →
      (∀ j : Nat, buffers.early.block ≠ (TensorInstance.record pool j).block) →
      (∀ j : Nat, buffers.last.block ≠ (TensorInstance.record pool j).block) →
      0 < Binary64.value step →
      StepGuards.Progress time (Binary64.addResult time step) →
      ¬ StepGuards.AboveStop (Binary64.addResult time step) stop →
      ¬ StepAdmission.AdmittedDuration step →
      load heap ((TensorInstance.record pool i).member "logger") = some (.pointer (some logger)) →
      load heap ((TensorInstance.record pool i).member "logging") = some (.integer 1) →
      load heap ((TensorInstance.record pool i).member "environment") = some (.pointer environment) → ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some (TensorInstance.record pool i))
          (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
      (∃ events value after, foreign.execute (StepDiscard.arguments environment category text)
        (StepEntry.outputHeap heap buffers time) events value after ∧
        behavior = .terminates events ⟨.integer 2, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (StepDiscard.arguments environment category text)
        (StepEntry.outputHeap heap buffers time) events value after) ∧ behavior = .wrong [])

set_option maxRecDepth 100000 in
theorem discard_logged_behaviors (header : CFenv.Header) :
    DiscardLogged header := by
  letI : CInterface := TensorDoStep.fenvInterface (static := static) header
  intro E program types heap pool i buffers point step time flag stop oldOutput text category logger environment name
    foreign rounding floorBound defined categoryBound textBound address external prototype kindValue modeValue timeCell
    same enabled limit event terminate early last outsideEvent outsideTerminate outsideEarly outsideLast positive
    progress noStop offGrid loggerValue loggingValue environmentValue behavior
  set p := TensorInstance.record pool i with hp
  have loaded (name : String) :
      load (StepEntry.outputHeap heap buffers time) (p.member name) = load heap (p.member name) := by
    simp only [load, StepEntry.output_instance heap buffers time p (p.member name)
      (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i) rfl]
  obtain ⟨env, gtypes, rest, reached, instanceValue, statusValue⟩ :=
    discard_prefix header program types heap pool i buffers point step time flag stop oldOutput
      rounding floorBound defined kindValue modeValue timeCell same enabled limit event terminate early last
      outsideEvent outsideTerminate outsideEarly outsideLast positive progress noStop offGrid
  have result := StepDiscard.all_behaviors (TensorDoStep.fenvErrorContext header) program env gtypes rest
    (StepEntry.outputHeap heap buffers time) p text category logger environment name foreign instanceValue statusValue
    ((loaded "logger").trans loggerValue) ((loaded "logging").trans loggingValue)
    ((loaded "environment").trans environmentValue) address categoryBound textBound external prototype
  exact (reached.silent_finite_behaviors (by intro history divergent; have impossible := (result (.diverges history)).mp divergent; simp at impossible) behavior).trans (result behavior)

end


/-! ### Consumable function contract

This mirrors the tensor `fmi3DoStep` contract shape: the printed function text, its
declaration closedness, its printed-text denotation under the shared C printer, the
null-handle rejection, the accepted end-to-end execution over the constant-rate
instance record (`execution`), and, under the same C floating-environment guard
premises, the off-grid `fmi3Discard` path with logging suppressed and enabled
(`discarded`). The lifecycle rejection (`lifecycle_behaviors`) is a companion
theorem. -/

section
open CTree.Printer
variable [static : StaticLiterals]
private local instance contractInterface : CInterface := cInterface static.addresses

/-- The constant-rate `fmi3DoStep` function contract, parameterized on the C
floating-environment header its accepted and discard paths run under. -/
structure Contract (header : CFenv.Header) (text : String) : Prop where
  printed : text = function.render
  closed : function.body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text function
  rejected : ∀ {E} (program : CCalls.Events.Program E) (types : StepEntry.Types) (heap : Heap)
    (point step : BitVec 64) (flag : Bool) (outputs : StepEntry.Outputs),
    program.internal.definitions "fmi3DoStep" = some (.tree function) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3DoStep" (StepEntry.arguments none point step flag outputs) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩
  execution : ExecutionFree header
  discarded : DiscardSuppressed header ∧ DiscardLogged header

theorem contract (header : CFenv.Header) : Contract header function.render where
  printed := rfl
  closed := doStepBody_closed
  denotes := function_denotes
  rejected program types heap point step flag outputs defined :=
    null_behaviors program types heap point step flag outputs defined
  execution := execution_free header
  discarded := ⟨discard_suppressed_behaviors header, discard_logged_behaviors header⟩

end

end Rumoca.FMI3.ConstantDoStep
