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
