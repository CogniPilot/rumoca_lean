import RumocaFMI3.TensorContinuousStates
import RumocaFMI3.ConstantInstanceRhs

/-! Constant-rate `fmi3GetContinuousStateDerivatives` body over the static
constant-rate instance record, as a package-checked product.

The constant-rate profile (`G01`) has no input tensor: its derivative is the
constant rate vector, written by the emitted numerical entry
`rumoca_constant_rhs(double *der)` (`packages/backend-c/RumocaC/ConstantKernelCode.lean`),
whose only argument is the instance's derivative region `&(m->dx[0])`. The body
guards, checks the count, calls that entry to write `der(x)`, then copies the
written `der(x)` region into the caller's buffer with the shared copy suffix
(`TensorContinuousStates.derivCopyTail`). It reuses the tensor derivative
getter's guard, count check, parameters, copy suffix and copy-delivery theorem
verbatim; only the entry call differs (`rumoca_constant_rhs` with the single
derivative pointer, in place of `rumoca_rhs(x, u, dx, count)`).

The copy suffix delivers whatever the entry wrote into `der(x)`; the target
semantics of the entry are the constant-rate kernel contract
(`Rumoca.CConstant.contract_correct`), which specifies that each written
derivative is the round-to-nearest-even of its decimal-literal rate. The fused
single-run observable execution of the numerical entry
(`ConstantInstanceRhs.rhs_writes_events`, the constant analog of the tensor
`TensorInstanceRhs.derivative_writes_events`) composes the guard prefix, the entry
run and the copy suffix as one observable-machine execution: `deriv_behaviors`
proves the getter's sole terminating behavior returns `fmi3OK` with the exactly
rounded rate vector delivered to the caller buffer, the instance's `der(x)` region
holding the same values, and every other instance preserved. Its `double *`
header-typing premise records the interface obligation the numerical entry needs,
carried like the tensor getter's `Library` premise. This product also proves the
getter's printed text, closedness, denotation and null rejection.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and the tensor and scalar adapters, `Runtime.lean` and
every existing contract are unchanged. Every theorem is universal in the state
shape. -/
noncomputable section
namespace Rumoca.FMI3.ConstantDerivative
open CTree CMemory CBody CLoops
open Rumoca.CMemory.TensorView Rumoca.CMemory.TensorRegion Rumoca.FMI3.TensorInstance
open Rumoca.FMI3.TensorContinuousStates (derivParameters derivGuardEnv derivCountReject derivCopyTail
  derivParameters_bound deriv_delivers derivSignature_printable)

/-- The C arguments of the constant-rate derivative entry: a pointer to the
instance's derivative region `&(m->dx[0])`. The rate vector needs no state or
input, so the entry takes only the written region. -/
def entryArgs : List Expr := [Runtime.region derivativeName]

def derivBody (shape : Tensor.Shape) : List Stmt :=
  Runtime.require .getDerivatives ++
    (derivCountReject shape.volume :: .eval (Runtime.call "rumoca_constant_rhs" entryArgs) ::
      derivCopyTail shape)

def derivFunction (shape : Tensor.Shape) : CTree.Function :=
  ⟨DerivativeCalls.signature, derivBody shape, false⟩

theorem derivBody_closed (shape : Tensor.Shape) :
    (derivFunction shape).body.all CBodyEmbedding.closedBlocks = true := by
  simp [derivFunction, derivBody, derivCopyTail, derivCountReject, entryArgs,
    TensorFloat64.getLoopSuffix, TensorFloat64.getCopyBody, Runtime.require, Runtime.instancePrefix,
    Runtime.modeGuard, Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, Runtime.ok,
    Runtime.field, Runtime.v, Runtime.n, Runtime.region, Runtime.call, CBodyEmbedding.closedBlocks,
    CLoops.noDeclarations, CLoops.loop, CLoops.counterStep]

/-! ### Printed-text denotation -/

section
open CTree.Printer CTree.Syntax

set_option maxHeartbeats 4000000 in
theorem derivBody_printable (shape : Tensor.Shape) :
    ∀ stmt ∈ (derivFunction shape).body, ItemPrintable RuntimePrinter.typedefs stmt := by
  have iType : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
    .pointer (text := "Instance") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have fType : TypeSpelling RuntimePrinter.typedefs "fmi3Float64 *" :=
    .pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have sType : TypeSpelling RuntimePrinter.typedefs "size_t" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  simp only [derivFunction, derivBody, derivCopyTail, derivCountReject, entryArgs,
      TensorFloat64.getLoopSuffix, Runtime.region, Runtime.require, Runtime.instancePrefix,
      Runtime.modeGuard, Runtime.allowedExpression, permittedModes, Runtime.reject, Runtime.branch,
      Runtime.fail, Runtime.ret, Runtime.ok, Runtime.field, Runtime.v, Runtime.n, Runtime.eqv,
      Runtime.nev, Runtime.both, Runtime.either, Runtime.negate, Runtime.any, Runtime.mode, Runtime.lt,
      Runtime.call, TensorFloat64.getCopyBody, TensorFloat64.srcCell, Float64Calls.output,
      CLoops.loop, CLoops.counterStep, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, List.forall_mem_nil, or_false, or_imp, forall_and,
      List.cons_append, List.nil_append, forall_eq] <;>
    repeat first
      | exact CNull.literal_printable _
      | exact iType
      | exact fType
      | exact sType
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

/-- The rendered derivative getter denotes its function under the shared C printer. -/
theorem derivFunction_denotes (shape : Tensor.Shape) :
    FunctionDenotes RuntimePrinter.typedefs (derivFunction shape).render (derivFunction shape) :=
  CTree.Printer.function_denotes ⟨derivSignature_printable, derivBody_printable shape⟩

end

/-! ### Null-handle rejection and copy-suffix delivery -/

section
variable [static : StaticLiterals]
private local instance derivInterface : CInterface := cInterface static.addresses

/-- A null instance handle is rejected with `fmi3Error`, changing nothing. -/
theorem null_deriv_behaviors (shape : Tensor.Shape) (program : CCalls.Events.Program E) (heap : Heap)
    (buffer : Option Address) (count : UInt64)
    (defined : program.internal.definitions "fmi3GetContinuousStateDerivatives" =
      some (.tree (derivFunction shape)))
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetContinuousStateDerivatives" (DerivativeCalls.values none buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (derivFunction shape)
    (Runtime.modeGuard .getDerivatives :: derivCountReject shape.volume ::
      .eval (Runtime.call "rumoca_constant_rhs" entryArgs) :: derivCopyTail shape)
    (DerivativeCalls.values none buffer count) (derivParameters none buffer count) heap defined
    (derivParameters_bound _ _ _)
    (by simp [derivFunction, derivBody, Runtime.require, List.append_assoc])
    rfl (derivBody_closed shape)
  all_goals simp [derivParameters, CBody.bind]

variable (program : CCalls.Events.Program E)

/-- The derivative getter's copy suffix over any heap whose `der(x)` region holds
the finite rate vector `result` (the situation the numerical entry
`rumoca_constant_rhs` establishes): it delivers `result` into the caller buffer in
row-major order and changes no other cell. This is the tensor derivative getter's
copy-delivery theorem at the constant-rate profile; the derivative getter shares
that copy suffix verbatim. -/
theorem deriv_copy_delivers (shape : Tensor.Shape) (H : Heap) (p buffer : Address) (count : UInt64)
    (types0 : Types) (result : Values shape) (stack : CCalls.Typed.Continuation)
    (bounded : shape.volume < 2 ^ 64)
    (readable : Reads H (p.member derivativeName) result)
    (writable : Writable H buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume, (p.member derivativeName).index a ≠ buffer.index b) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (derivCopyTail shape) (derivGuardEnv p buffer count) types0 H) "fmi3Status" stack)
      (.returning (.integer 0) (written H buffer result shape.volume) stack) :=
  deriv_delivers program shape H p buffer count types0 result stack bounded readable writable separate

/-- The derivative getter's copy suffix over instance `i`, after the entry has
written `der(x) = derivatives`: it delivers `derivatives` into the caller buffer,
leaving every other cell of the written heap unchanged. -/
theorem deriv_instance_delivers (backing : Heap) (pool : Address) (i : Nat) (shape oshape : Tensor.Shape)
    (time : Values Tensor.scalar) (state input : Values shape) (output : Option (Values oshape))
    (derivatives : Values shape) (buffer : Address) (count : UInt64) (types0 : Types)
    (stack : CCalls.Typed.Continuation) (bounded : shape.volume < 2 ^ 64)
    (writable : Writable (written (TensorInstance.store backing pool i shape oshape time state input output)
      (TensorInstance.field pool i derivativeName) derivatives shape.volume) buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i derivativeName).index a ≠ buffer.index b) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (derivCopyTail shape) (derivGuardEnv (TensorInstance.record pool i) buffer count) types0
        (written (TensorInstance.store backing pool i shape oshape time state input output)
          (TensorInstance.field pool i derivativeName) derivatives shape.volume)) "fmi3Status" stack)
      (.returning (.integer 0)
        (written (written (TensorInstance.store backing pool i shape oshape time state input output)
          (TensorInstance.field pool i derivativeName) derivatives shape.volume) buffer derivatives shape.volume)
        stack) :=
  deriv_copy_delivers program shape _ (TensorInstance.record pool i) buffer count types0 derivatives stack bounded
    (written_reads _ (TensorInstance.field pool i derivativeName) derivatives) writable separate

/-! ### The fused single-run constant derivative getter -/

/-- The entry-call step: from the checked prefix the observable scheduler enters
the constant-rate derivative entry `rumoca_constant_rhs`, resolved directly by
name, with the instance's `der(x)` region pointer as its only argument and the
copy suffix saved as the caller continuation. -/
theorem constant_deriv_enter (shape : Tensor.Shape) (p buffer : Address) (count : UInt64)
    (types0 : Types) (H : Heap) (rest : List Stmt) (stack : CCalls.Typed.Continuation) :
    CCalls.Events.internalNext program
      (.body (.running (.eval (Runtime.call "rumoca_constant_rhs" entryArgs) :: rest)
        (derivGuardEnv p buffer count) types0 H) "fmi3Status" stack) =
      some (.calling "rumoca_constant_rhs" [.pointer (some (p.member derivativeName))] H
        (.caller .discard rest (derivGuardEnv p buffer count) types0 "fmi3Status" stack)) := by
  simp [CCalls.Events.internalNext, CCalls.Typed.nextWith, CLoops.next, CLoops.eval,
    entryArgs, Runtime.call, Runtime.region, Runtime.field, Runtime.v, Runtime.n, CBody.eval,
    CBody.lvalue, CCalls.Events.enterCall, CCalls.Events.resolve, CCalls.Indirect.operand,
    CCalls.Indirect.resolve, CCalls.arguments, derivGuardEnv, derivParameters, CBody.bind,
    CBody.resolve, CBody.constants, Value.address]

/-- The fused single-run constant derivative getter over instance `i`: guarding,
checking the count, invoking the constant kernel entry `rumoca_constant_rhs`
through the transfer lemma, then copying the written `der(x)` region into the
caller buffer, all as one observable-machine execution. It reaches `fmi3OK` with
the caller buffer holding the exactly rounded rate vector, the instance's `der(x)`
region holding the same values, and every other cell of every other instance
preserved. The `ptrTy` premise records the `double *` header typing the numerical
entry needs, and `resolves` that the constant entry's call sites resolve directly
by name. -/
theorem deriv_reaches (shape : Tensor.Shape) (rates : List Rumoca.ConstantProfile.Decimal)
    (len : rates.length = shape.volume) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (found : definitions "rumoca_constant_rhs" = some (Rumoca.CConstant.rhsFunction rates))
    (ptrTy : (cInterface static.addresses).types "double *" = some .pointer)
    (backing : Heap) (pool : Address) (i : Nat)
    (time : Values Tensor.scalar) (state : Values shape)
    (buffer : Address) (count : UInt64) (kind : Kind) (mode : Mode) (stack : CCalls.Typed.Continuation)
    (matched : count.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetContinuousStateDerivatives" =
      some (.tree (derivFunction shape)))
    (hk : load (TensorInstance.constantStore backing pool i shape time state)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.constantStore backing pool i shape time state)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives kind mode)
    (writable : Writable (TensorInstance.constantStore backing pool i shape time state) buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i derivativeName).index a ≠ buffer.index b)
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling "rumoca_constant_rhs" [.pointer (some (TensorInstance.field pool i derivativeName))]
        (TensorInstance.constantStore backing pool i shape time state) .done) v →
      CCalls.Events.Resolves program v) :
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i derivativeName)
        (ConstantInstanceRhs.ratesVec rates shape len) ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) =
          (TensorInstance.constantStore backing pool i shape time state) ((TensorInstance.field pool j b).index k)) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling "fmi3GetContinuousStateDerivatives"
          (DerivativeCalls.values (some (TensorInstance.record pool i)) (some buffer) count)
          (TensorInstance.constantStore backing pool i shape time state) stack)
        (.returning (.integer 0)
          (written finalHeap buffer (ConstantInstanceRhs.ratesVec rates shape len) shape.volume) stack) := by
  set H := TensorInstance.constantStore backing pool i shape time state with hH
  set m := TensorInstance.record pool i with hm'
  have accepted := LifecycleGuard.accept (derivParameters (some m) (some buffer) count) H m
    .getDerivatives kind mode
    (derivCountReject shape.volume :: .eval (Runtime.call "rumoca_constant_rhs" entryArgs) :: derivCopyTail shape)
    (by simp [derivParameters, CBody.bind]) (by simp [derivParameters, CBody.bind]) hk hm allowed
  have prefixRun : CBody.run 4 (.running (derivBody shape) (derivParameters (some m) (some buffer) count) H) =
      some (.running (.eval (Runtime.call "rumoca_constant_rhs" entryArgs) :: derivCopyTail shape)
        (derivGuardEnv m buffer count) H) := by
    rw [derivBody]
    rw [show (4 : Nat) = 3 + 1 from rfl, CBody.run_add, accepted, Option.bind_some]
    exact TensorFloat64.run_one (TensorFloat64.reject_false (derivGuardEnv m buffer count) H
      (Runtime.any [Runtime.nev (Runtime.v "nContinuousStates") (Runtime.n shape.volume),
        Runtime.negate (Runtime.v "derivatives")]) "Invalid continuous state count or pointer"
      (.eval (Runtime.call "rumoca_constant_rhs" entryArgs) :: derivCopyTail shape)
      (TensorContinuousStates.derivCount_pass H m buffer count shape.volume matched))
  obtain ⟨types0, entered⟩ := CCalls.Events.body_prefix_reaches program (derivFunction shape)
    (DerivativeCalls.values (some m) (some buffer) count) (derivParameters (some m) (some buffer) count)
    (derivGuardEnv m buffer count) H H
    (.eval (Runtime.call "rumoca_constant_rhs" entryArgs) :: derivCopyTail shape) stack 4 defined
    (derivParameters_bound _ _ _) (derivBody_closed shape) prefixRun
  have enterStep : CCalls.Events.internalNext program
      (.body (.running (.eval (Runtime.call "rumoca_constant_rhs" entryArgs) :: derivCopyTail shape)
        (derivGuardEnv m buffer count) types0 H) "fmi3Status" stack) =
      some (.calling "rumoca_constant_rhs" [.pointer (some (m.member derivativeName))] H
        (.caller .discard (derivCopyTail shape) (derivGuardEnv m buffer count) types0 "fmi3Status" stack)) :=
    constant_deriv_enter program shape m buffer count types0 H (derivCopyTail shape) stack
  obtain ⟨finalHeap, reads, _writableDeriv, frame, others, ran⟩ :=
    ConstantInstanceRhs.rhs_writes_events (shape := shape) rates len definitions program linked found ptrTy H pool i
      (by rw [hH]; exact TensorInstance.constant_writable_derivative backing pool i shape time state) resolves
      (.caller .discard (derivCopyTail shape) (derivGuardEnv m buffer count) types0 "fmi3Status" stack)
  have resumeStep : CCalls.Events.internalNext program
      (.returning .void finalHeap
        (.caller .discard (derivCopyTail shape) (derivGuardEnv m buffer count) types0 "fmi3Status" stack)) =
      some (.body (.running (derivCopyTail shape) (derivGuardEnv m buffer count) types0 finalHeap)
        "fmi3Status" stack) := by
    simp [CCalls.Events.internalNext, CCalls.Typed.nextWith, CCalls.Typed.resume]
  have writableFinal : Writable finalHeap buffer shape.volume := by
    intro b hb
    obtain ⟨old, ho⟩ := writable b hb
    exact ⟨old, (frame (buffer.index b) (fun mIdx hmIdx => (separate mIdx hmIdx b hb).symm)).trans ho⟩
  have deliver := deriv_copy_delivers program shape finalHeap m buffer count types0
    (ConstantInstanceRhs.ratesVec rates shape len) stack bounded reads writableFinal separate
  exact ⟨finalHeap, reads, others, entered.trans (.next enterStep (ran.trans (.next resumeStep deliver)))⟩

/-- The fused constant derivative getter's sole terminating observable behavior
over instance `i`: it returns `fmi3OK` with the exactly rounded rate vector
delivered to the caller buffer, the instance's `der(x)` region holding the same
values, and every other cell of every other instance preserved. -/
theorem deriv_behaviors (shape : Tensor.Shape) (rates : List Rumoca.ConstantProfile.Decimal)
    (len : rates.length = shape.volume) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (found : definitions "rumoca_constant_rhs" = some (Rumoca.CConstant.rhsFunction rates))
    (ptrTy : (cInterface static.addresses).types "double *" = some .pointer)
    (backing : Heap) (pool : Address) (i : Nat)
    (time : Values Tensor.scalar) (state : Values shape)
    (buffer : Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (matched : count.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetContinuousStateDerivatives" =
      some (.tree (derivFunction shape)))
    (hk : load (TensorInstance.constantStore backing pool i shape time state)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.constantStore backing pool i shape time state)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives kind mode)
    (writable : Writable (TensorInstance.constantStore backing pool i shape time state) buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i derivativeName).index a ≠ buffer.index b)
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling "rumoca_constant_rhs" [.pointer (some (TensorInstance.field pool i derivativeName))]
        (TensorInstance.constantStore backing pool i shape time state) .done) v →
      CCalls.Events.Resolves program v) :
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i derivativeName)
        (ConstantInstanceRhs.ratesVec rates shape len) ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) =
          (TensorInstance.constantStore backing pool i shape time state) ((TensorInstance.field pool j b).index k)) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3GetContinuousStateDerivatives"
          (DerivativeCalls.values (some (TensorInstance.record pool i)) (some buffer) count)
          (TensorInstance.constantStore backing pool i shape time state) .done) behavior ↔
        behavior = .terminates []
          ⟨.integer 0, written finalHeap buffer (ConstantInstanceRhs.ratesVec rates shape len) shape.volume⟩ := by
  obtain ⟨finalHeap, reads, others, ran⟩ :=
    deriv_reaches program shape rates len definitions linked found ptrTy backing pool i time state buffer count
      kind mode .done matched bounded defined hk hm allowed writable separate resolves
  exact ⟨finalHeap, reads, others, fun behavior =>
    (CCalls.Events.internal_prefix program ran (CCalls.Events.return_forced program _ _)).behaviors behavior⟩

end

/-! ### Consumable derivative-getter contract

This mirrors the tensor derivative-getter contract: the printed function text, its
declaration closedness, its printed-text denotation under the shared C printer, the
null-handle rejection, the copy-suffix delivery of whatever `der(x)` holds after
the numerical entry ran, and the fused single-run execution that composes the guard
prefix, the constant kernel entry and the copy suffix into the getter's sole
terminating behavior. -/

section
open CTree.Printer
variable [static : StaticLiterals]
private local instance contractInterface : CInterface := cInterface static.addresses

/-- The copy-suffix delivery of the constant-rate derivative getter, universal in
the heap that already holds the finite derivative in `der(x)`. -/
def DerivDelivers (shape : Tensor.Shape) : Prop :=
  ∀ {E} (program : CCalls.Events.Program E) (H : Heap) (p buffer : Address) (count : UInt64)
    (types0 : Types) (result : Values shape) (stack : CCalls.Typed.Continuation),
    shape.volume < 2 ^ 64 →
    Reads H (p.member derivativeName) result →
    Writable H buffer shape.volume →
    (∀ a < shape.volume, ∀ b < shape.volume, (p.member derivativeName).index a ≠ buffer.index b) →
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (derivCopyTail shape) (derivGuardEnv p buffer count) types0 H) "fmi3Status" stack)
      (.returning (.integer 0) (written H buffer result shape.volume) stack)

theorem deriv_delivers_holds (shape : Tensor.Shape) : DerivDelivers shape :=
  fun program H p buffer count types0 result stack bounded readable writable separate =>
    deriv_copy_delivers program shape H p buffer count types0 result stack bounded readable writable separate

/-- The fused single-run execution of the constant derivative getter: it delivers
the exactly rounded rate vector into the caller buffer, the instance's `der(x)`
region holding the same values, and every other instance preserved. The `double *`
header-typing premise records the interface obligation the numerical entry needs,
carried like the tensor getter's `Library` premise; the bodies contain no nested
calls, so the loop-call `resolves` premise holds definitionally at every reachable
state and is carried only to mirror the tensor entry theorems. -/
def DerivExecution (shape : Tensor.Shape) : Prop :=
  ∀ {E} (program : CCalls.Events.Program E) (definitions : CLoops.Calls.Definitions)
    (rates : List Rumoca.ConstantProfile.Decimal) (len : rates.length = shape.volume),
    CCalls.Typed.Extends definitions program.internal →
    definitions "rumoca_constant_rhs" = some (Rumoca.CConstant.rhsFunction rates) →
    (cInterface static.addresses).types "double *" = some .pointer →
    ∀ (backing : Heap) (pool : Address) (i : Nat) (time : Values Tensor.scalar) (state : Values shape)
      (buffer : Address) (count : UInt64) (kind : Kind) (mode : Mode),
    count.toNat = shape.volume → shape.volume < 2 ^ 64 →
    program.internal.definitions "fmi3GetContinuousStateDerivatives" = some (.tree (derivFunction shape)) →
    load (TensorInstance.constantStore backing pool i shape time state)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code) →
    load (TensorInstance.constantStore backing pool i shape time state)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code) →
    Reference.Allowed .getDerivatives kind mode →
    Writable (TensorInstance.constantStore backing pool i shape time state) buffer shape.volume →
    (∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i derivativeName).index a ≠ buffer.index b) →
    (∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling "rumoca_constant_rhs" [.pointer (some (TensorInstance.field pool i derivativeName))]
        (TensorInstance.constantStore backing pool i shape time state) .done) v →
      CCalls.Events.Resolves program v) →
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i derivativeName)
        (ConstantInstanceRhs.ratesVec rates shape len) ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) =
          (TensorInstance.constantStore backing pool i shape time state) ((TensorInstance.field pool j b).index k)) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3GetContinuousStateDerivatives"
          (DerivativeCalls.values (some (TensorInstance.record pool i)) (some buffer) count)
          (TensorInstance.constantStore backing pool i shape time state) .done) behavior ↔
        behavior = .terminates []
          ⟨.integer 0, written finalHeap buffer (ConstantInstanceRhs.ratesVec rates shape len) shape.volume⟩

theorem deriv_execution_holds (shape : Tensor.Shape) : DerivExecution shape :=
  fun program definitions rates len linked found ptrTy backing pool i time state buffer count kind mode
      matched bounded defined hk hm allowed writable separate resolves =>
    deriv_behaviors program shape rates len definitions linked found ptrTy backing pool i time state buffer count
      kind mode matched bounded defined hk hm allowed writable separate resolves

/-- The constant-rate `fmi3GetContinuousStateDerivatives` function contract. -/
structure DerivContract (shape : Tensor.Shape) (text : String) : Prop where
  printed : text = (derivFunction shape).render
  closed : (derivFunction shape).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text (derivFunction shape)
  rejected : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (buffer : Option Address) (count : UInt64),
    program.internal.definitions "fmi3GetContinuousStateDerivatives" = some (.tree (derivFunction shape)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetContinuousStateDerivatives" (DerivativeCalls.values none buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩
  delivers : DerivDelivers shape
  execution : DerivExecution shape

theorem deriv_contract (shape : Tensor.Shape) : DerivContract shape (derivFunction shape).render where
  printed := rfl
  closed := derivBody_closed shape
  denotes := derivFunction_denotes shape
  rejected program heap buffer count defined := null_deriv_behaviors shape program heap buffer count defined
  delivers := deriv_delivers_holds shape
  execution := deriv_execution_holds shape

end

end Rumoca.FMI3.ConstantDerivative
