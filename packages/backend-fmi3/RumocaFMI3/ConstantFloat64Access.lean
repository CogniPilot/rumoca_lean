import RumocaFMI3.TensorFloat64Access
import RumocaFMI3.ConstantDerivative

/-! Constant-rate `fmi3GetFloat64` / `fmi3SetFloat64` bodies over the static
constant-rate instance record, as package-checked products.

The constant-rate profile (`G01`) exposes no input tensor and no dense output.
Its value references are renumbered without the input: `0` the independent time
base (element count 1), `1` the state vector `x`, `2` the state derivative
`der(x)` (each element count `shape.volume`). The getter denotes any of the
three references; the setter admits only the state reference `1` (writable) and
rejects the derivative reference `2` as read-only, matching the constant-rate
model description (`TensorMetadata.constantModelDescription`, `1` state, `2`
derivative). The derivative is a calculated variable: before staging reference
`2` the getter evaluates it through the constant kernel entry
(`ConstantDerivative.entryCall`), as the derivative getter does, so the returned
value is the rate vector whatever the region held before. The shared request-check, staging, copy-loop and finiteness
machinery of the tensor accessor (`Rumoca.FMI3.TensorFloat64`) is reused verbatim;
only the value-reference dispatch differs. The copy uses one counted `size_t`
loop over the symbolic state count, so no coordinate is enumerated.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and the tensor and scalar adapters, `Runtime.lean` and
every existing contract are unchanged. Every theorem is universal in the state
shape. -/
noncomputable section
namespace Rumoca.FMI3.ConstantFloat64
open CTree CMemory CBody CLoops
open Rumoca.FMI3.TensorInstance
open Rumoca.CMemory.TensorView
open Rumoca.FMI3.TensorFloat64 (vr0 getArm memberPointer getLoopSuffix basicReject countReject
  setArm setLoopSuffix validateBody getCopyBody setCopyBody srcCell dstCell)
open Rumoca.FMI3.Float64Calls (signature parameters arguments parameters_bound output)

/-! ### The getter body -/

/-- Dispatch tail for reference 2 (the derivative `der(x)`). -/
def getDispatch2 (shape : Tensor.Shape) : List Stmt :=
  [Runtime.branch (Runtime.eqv vr0 (Runtime.n 2))
    (ConstantDerivative.entryCall :: getArm derivativeName shape.volume)
    [Runtime.fail "Unknown value reference"]]

/-- Dispatch tail for references 1 and above (the state `x`). -/
def getDispatch1 (shape : Tensor.Shape) : List Stmt :=
  [Runtime.branch (Runtime.eqv vr0 (Runtime.n 1)) (getArm stateName shape.volume)
    (getDispatch2 shape)]

/-- Dispatch one value reference to its region, staging its pointer and count:
`0` time (count 1), `1` state, `2` derivative; every other reference fails. -/
def getDispatch (shape : Tensor.Shape) : Stmt :=
  Runtime.branch (Runtime.eqv vr0 (Runtime.n 0)) (getArm timeName 1) (getDispatch1 shape)

/-- The constant-rate getter dispatch arms as a value-reference list: references
`0..2` staging the time, state and derivative regions. The constant getter is the
generic `Float64Dispatch.dispatchChain` over this list. -/
def getArms (shape : Tensor.Shape) : List (Nat × List Stmt) :=
  [(0, getArm timeName 1), (1, getArm stateName shape.volume), (2, ConstantDerivative.entryCall :: getArm derivativeName shape.volume)]

theorem getDispatch_chain (shape : Tensor.Shape) :
    Float64Dispatch.dispatchChain vr0 (getArms shape)
        [Runtime.fail "Unknown value reference"] = [getDispatch shape] := rfl

/-- The statements after the guard, run in the typed machine. -/
def getRest (shape : Tensor.Shape) : List Stmt :=
  [.declare "fmi3Float64 *" "src" Expr.nullPointer, .declare "size_t" "expected" (Runtime.n 0),
    getDispatch shape, countReject] ++ getLoopSuffix

def getBody (shape : Tensor.Shape) : List Stmt :=
  Runtime.require .get ++ (basicReject :: getRest shape)

def getFunction (shape : Tensor.Shape) : CTree.Function :=
  ⟨signature false, getBody shape, false⟩

theorem getBody_closed (shape : Tensor.Shape) :
    (getFunction shape).body.all CBodyEmbedding.closedBlocks = true := by
  simp [getFunction, getBody, getRest, getDispatch, getDispatch1, getDispatch2, basicReject, countReject,
    getLoopSuffix, getArm, ConstantDerivative.entryCall, ConstantDerivative.entryArgs, Runtime.call,
    Runtime.region, Runtime.field, Runtime.v, Runtime.n, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject,
    Runtime.branch, Runtime.fail, Runtime.ret, Runtime.ok, getCopyBody, CBodyEmbedding.closedBlocks,
    CLoops.noDeclarations, CLoops.loop, CLoops.counterStep]

/-! ### The setter body -/

/-- The constant-rate setter dispatch: only the state `x` (reference `1`) is
writable. The time base and derivative are read-only, so every other reference
fails. -/
def setDispatch (shape : Tensor.Shape) : Stmt :=
  Runtime.branch (Runtime.eqv vr0 (Runtime.n 1)) (setArm stateName shape.volume)
    [Runtime.fail "Unknown or read-only value reference"]

/-- The constant-rate setter dispatch arms: only the state `x` (reference `1`) is
writable. The constant setter is the generic `Float64Dispatch.dispatchChain` over
this single-arm list. -/
def setArms (shape : Tensor.Shape) : List (Nat × List Stmt) :=
  [(1, setArm stateName shape.volume)]

theorem setDispatch_chain (shape : Tensor.Shape) :
    Float64Dispatch.dispatchChain vr0 (setArms shape)
        [Runtime.fail "Unknown or read-only value reference"] = [setDispatch shape] := rfl

def setRest (shape : Tensor.Shape) : List Stmt :=
  [.declare "fmi3Float64 *" "dst" Expr.nullPointer, .declare "size_t" "expected" (Runtime.n 0),
    setDispatch shape, countReject] ++ setLoopSuffix

def setBody (shape : Tensor.Shape) : List Stmt :=
  Runtime.require .setStart ++ (basicReject :: setRest shape)

def setFunction (shape : Tensor.Shape) : CTree.Function :=
  ⟨signature true, setBody shape, false⟩

theorem setBody_closed (shape : Tensor.Shape) :
    (setFunction shape).body.all CBodyEmbedding.closedBlocks = true := by
  simp [setFunction, setBody, setRest, setDispatch, basicReject, countReject, setLoopSuffix, setArm,
    validateBody, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject,
    Runtime.branch, Runtime.fail, Runtime.ret, Runtime.ok, setCopyBody, CBodyEmbedding.closedBlocks,
    CLoops.noDeclarations, CLoops.loop, CLoops.counterStep]

/-! ### Printed-text denotation -/

section
open CTree.Printer CTree.Syntax

/-- Each constant-rate getter dispatch arm prints its intended C token grammar;
supplied to the generic `dispatchChain_printable`. -/
theorem getArms_printable (shape : Tensor.Shape) :
    ∀ a ∈ getArms shape, ∀ stmt ∈ a.2, ItemPrintable RuntimePrinter.typedefs stmt := by
  intro a ha
  simp only [getArms, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact TensorFloat64.getArm_printable timeName 1 (by decide +kernel)
  · exact TensorFloat64.getArm_printable stateName shape.volume (by decide +kernel)
  · intro stmt member
    rcases List.mem_cons.mp member with rfl | staged
    · exact ConstantDerivative.entryCall_printable
    · exact TensorFloat64.getArm_printable derivativeName shape.volume (by decide +kernel) stmt staged

/-- The constant-rate setter dispatch arm prints its intended C token grammar. -/
theorem setArms_printable (shape : Tensor.Shape) :
    ∀ a ∈ setArms shape, ∀ stmt ∈ a.2, ItemPrintable RuntimePrinter.typedefs stmt := by
  intro a ha
  simp only [setArms, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl
  exact TensorFloat64.setArm_printable stateName shape.volume (by decide +kernel)

/-- The constant-rate getter dispatch prints its intended C token grammar,
obtained from the generic dispatch-chain lemma over references `0..2`. -/
theorem getDispatch_printable (shape : Tensor.Shape) :
    ItemPrintable RuntimePrinter.typedefs (getDispatch shape) := by
  have h := Float64Dispatch.dispatchChain_printable RuntimePrinter.typedefs vr0 (getArms shape)
    [Runtime.fail "Unknown value reference"] TensorFloat64.vr0_printable
    TensorFloat64.getFallback_printable (getArms_printable shape)
  exact h _ (by rw [getDispatch_chain]; simp)

/-- The constant-rate setter dispatch prints its intended C token grammar,
obtained from the generic dispatch-chain lemma over the single writable state
reference. -/
theorem setDispatch_printable (shape : Tensor.Shape) :
    ItemPrintable RuntimePrinter.typedefs (setDispatch shape) := by
  have h := Float64Dispatch.dispatchChain_printable RuntimePrinter.typedefs vr0 (setArms shape)
    [Runtime.fail "Unknown or read-only value reference"] TensorFloat64.vr0_printable
    TensorFloat64.setFallback_printable (setArms_printable shape)
  exact h _ (by rw [setDispatch_chain]; simp)

/-- Every statement of the getter body prints its intended C token grammar. The
body is the shared `TensorFloat64.getBodyFor` around the constant-rate dispatch,
so its printability is the shared proof instantiated at this profile's dispatch. -/
theorem getBody_printable (shape : Tensor.Shape) :
    ∀ stmt ∈ (getFunction shape).body, ItemPrintable RuntimePrinter.typedefs stmt :=
  TensorFloat64.getBodyFor_printable (getDispatch shape) (getDispatch_printable shape)

/-- Every statement of the setter body prints its intended C token grammar, as the
shared `TensorFloat64.setBodyFor` proof instantiated at the constant-rate dispatch. -/
theorem setBody_printable (shape : Tensor.Shape) :
    ∀ stmt ∈ (setFunction shape).body, ItemPrintable RuntimePrinter.typedefs stmt :=
  TensorFloat64.setBodyFor_printable (setDispatch shape) (setDispatch_printable shape)

/-- The rendered getter denotes its function under the shared C printer. -/
theorem getFunction_denotes (shape : Tensor.Shape) :
    FunctionDenotes RuntimePrinter.typedefs (getFunction shape).render (getFunction shape) :=
  CTree.Printer.function_denotes ⟨TensorFloat64.signature_printable false, getBody_printable shape⟩

/-- The rendered setter denotes its function under the shared C printer. -/
theorem setFunction_denotes (shape : Tensor.Shape) :
    FunctionDenotes RuntimePrinter.typedefs (setFunction shape).render (setFunction shape) :=
  CTree.Printer.function_denotes ⟨TensorFloat64.signature_printable true, setBody_printable shape⟩

end

/-! ### The derivative is evaluated when it is read -/

section
variable [static : StaticLiterals]
private local instance readInterface : CInterface := cInterface static.addresses
variable (program : CCalls.Events.Program E)

/-- Reading `der(x)` of instance `i`: the getter evaluates the rate vector through
the constant kernel entry, returns its exactly rounded values with `fmi3OK`, leaves
them in the `der(x)` region and preserves every other instance, whatever the region
held before the call. -/
theorem get_derivative_reaches (shape : Tensor.Shape) (rates : List Rumoca.ConstantProfile.Decimal)
    (len : rates.length = shape.volume) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (found : definitions "rumoca_constant_rhs" = some (Rumoca.CConstant.rhsFunction rates))
    (ptrTy : (cInterface static.addresses).types "double *" = some .pointer)
    (backing : Heap) (pool : Address) (i : Nat) (time : Values Tensor.scalar) (state : Values shape)
    (refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode) (stack : CCalls.Typed.Continuation)
    (nref : n.toNat = 1) (nval : m.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape)))
    (hk : load (TensorInstance.constantStore backing pool i shape time state)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.constantStore backing pool i shape time state)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (refRead : load (TensorInstance.constantStore backing pool i shape time state)
      (refs.index 0) = some (.integer 2))
    (writable : Writable (TensorInstance.constantStore backing pool i shape time state) buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i derivativeName).index a ≠ buffer.index b)
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling "rumoca_constant_rhs" [.pointer (some (TensorInstance.field pool i derivativeName))]
        (TensorInstance.constantStore backing pool i shape time state) .done) v →
      CCalls.Events.Resolves program v) :
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i derivativeName) (ConstantInstanceRhs.ratesVec rates shape len) ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) =
          (TensorInstance.constantStore backing pool i shape time state) ((TensorInstance.field pool j b).index k)) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling "fmi3GetFloat64" (arguments (some (TensorInstance.record pool i)) (some refs) (some buffer) n m)
          (TensorInstance.constantStore backing pool i shape time state) stack)
        (.returning (.integer 0)
          (written finalHeap buffer (ConstantInstanceRhs.ratesVec rates shape len) shape.volume) stack) := by
  let H := TensorInstance.constantStore backing pool i shape time state
  let p := TensorInstance.record pool i
  have closed : (TensorFloat64.getFunctionFor (getDispatch shape)).body.all CBodyEmbedding.closedBlocks = true :=
    getBody_closed shape
  obtain ⟨types0, entered⟩ := TensorFloat64.guard_reaches_for (getDispatch shape) closed program H p refs buffer
    n m kind mode defined hk hm allowed nref stack
  have declared := TensorFloat64.declares_reaches_for program (getDispatch shape)
    (TensorFloat64.guardEnv p refs buffer n m) types0 H stack
    (by simp [TensorFloat64.guardEnv, parameters, CBody.bind])
    (by simp [TensorFloat64.guardEnv, parameters, CBody.bind])
  have rv : resolve (TensorFloat64.declaredEnv (TensorFloat64.guardEnv p refs buffer n m)) "valueReferences" =
      some (.pointer (some refs)) := by
    simp [TensorFloat64.declaredEnv, TensorFloat64.guardEnv, parameters, CBody.bind, CBody.resolve]
  have armClosed : (ConstantDerivative.entryCall :: getArm derivativeName shape.volume).all
      CLoops.noDeclarations = true := by
    simp [ConstantDerivative.entryCall, TensorFloat64.getArm, CLoops.noDeclarations]
  have b0 := TensorFloat64.cbranch_false (TensorFloat64.declaredEnv (TensorFloat64.guardEnv p refs buffer n m))
    (TensorFloat64.declaredTypes types0) H _ (getArm timeName 1) (getDispatch1 shape)
    (countReject :: TensorFloat64.getLoopSuffix)
    (by simp [getDispatch1, getDispatch2, ConstantDerivative.entryCall, TensorFloat64.getArm, Runtime.branch,
      Runtime.fail, Runtime.ret, CLoops.noDeclarations])
    (TensorFloat64.cvr0_ne _ _ H refs 2 0 rv refRead (by decide))
  have b1 := TensorFloat64.cbranch_false (TensorFloat64.declaredEnv (TensorFloat64.guardEnv p refs buffer n m))
    (TensorFloat64.declaredTypes types0) H _ (getArm stateName shape.volume) (getDispatch2 shape)
    (countReject :: TensorFloat64.getLoopSuffix)
    (by simp [getDispatch2, ConstantDerivative.entryCall, TensorFloat64.getArm, Runtime.branch,
      Runtime.fail, Runtime.ret, CLoops.noDeclarations])
    (TensorFloat64.cvr0_ne _ _ H refs 2 1 rv refRead (by decide))
  have b2 := TensorFloat64.cbranch_true (TensorFloat64.declaredEnv (TensorFloat64.guardEnv p refs buffer n m))
    (TensorFloat64.declaredTypes types0) H _ (ConstantDerivative.entryCall :: getArm derivativeName shape.volume)
    [Runtime.fail "Unknown value reference"] (countReject :: TensorFloat64.getLoopSuffix)
    (by simp [ConstantDerivative.entryCall, TensorFloat64.getArm, Runtime.fail, Runtime.ret,
      CLoops.noDeclarations])
    (TensorFloat64.cvr0_eq _ _ H refs 2 rv refRead)
  obtain ⟨finalHeap, reads, frame, others, ran⟩ := ConstantDerivative.entryCall_reaches program shape rates len
    definitions linked found ptrTy H pool i (TensorFloat64.declaredEnv (TensorFloat64.guardEnv p refs buffer n m))
    (TensorFloat64.declaredTypes types0) (getArm derivativeName shape.volume ++ (countReject :: TensorFloat64.getLoopSuffix))
    "fmi3Status" stack
    (by simp [TensorFloat64.declaredEnv, TensorFloat64.guardEnv, CBody.bind, p])
    (by simp [TensorFloat64.declaredEnv, TensorFloat64.guardEnv, parameters, CBody.bind])
    (TensorInstance.constant_writable_derivative backing pool i shape time state) resolves
  have writableFinal : Writable finalHeap buffer shape.volume := by
    intro b hb
    obtain ⟨old, ho⟩ := writable b hb
    exact ⟨old, (frame (buffer.index b) (fun k hk => (separate k hk b hb).symm)).trans ho⟩
  have staged := TensorFloat64.stage_reaches program (TensorFloat64.guardEnv p refs buffer n m) types0 finalHeap p
    (p.member derivativeName) derivativeName shape.volume (countReject :: TensorFloat64.getLoopSuffix) stack
    bounded (by simp [TensorFloat64.guardEnv, CBody.bind]) rfl
  have tail := TensorFloat64.get_tail_reaches program (TensorFloat64.guardEnv p refs buffer n m)
    (TensorFloat64.declaredTypes types0) finalHeap (p.member derivativeName) buffer shape
    (ConstantInstanceRhs.ratesVec rates shape len) m stack bounded nval
    (by simp [TensorFloat64.stagedEnv, CBody.bind, CBody.resolve])
    (by simp [TensorFloat64.stagedEnv, CBody.bind, CBody.resolve])
    (by simp [TensorFloat64.stagedEnv, TensorFloat64.declaredEnv, TensorFloat64.guardEnv, parameters, CBody.bind,
      CBody.resolve])
    (by simp [TensorFloat64.stagedEnv, TensorFloat64.declaredEnv, TensorFloat64.guardEnv, parameters, CBody.bind,
      CBody.resolve])
    (by simp [TensorFloat64.stagedEnv, TensorFloat64.declaredEnv, TensorFloat64.guardEnv, parameters, CBody.bind])
    (by simp [TensorFloat64.stagedEnv, TensorFloat64.declaredEnv, TensorFloat64.guardEnv, parameters, CBody.bind])
    reads writableFinal separate
  refine ⟨finalHeap, reads, others, entered.trans (declared.trans ?_)⟩
  exact .next (CCalls.Events.body_step program b0 _ stack)
    (.next (CCalls.Events.body_step program b1 _ stack)
      (.next (CCalls.Events.body_step program b2 _ stack) (ran.trans (staged.trans tail))))

end

/-! ### Null-handle rejections -/

section
variable [static : StaticLiterals]
private local instance rejectInterface : CInterface := cInterface static.addresses

/-- A null instance handle is rejected with `fmi3Error`, changing nothing. -/
theorem null_get_behaviors (shape : Tensor.Shape) (program : CCalls.Events.Program E) (heap : Heap)
    (refs buffer : Option Address) (n m : UInt64)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape)))
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments none refs buffer n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (getFunction shape)
    (Runtime.modeGuard .get :: basicReject :: getRest shape)
    (arguments none refs buffer n m) (parameters none refs buffer n m) heap defined
    (parameters_bound false _ _ _ _ _) (by simp [getFunction, getBody, Runtime.require, List.append_assoc])
    rfl (getBody_closed shape)
  all_goals simp [parameters, CBody.bind]

/-- A null instance handle is rejected with `fmi3Error`, changing nothing. -/
theorem null_set_behaviors (shape : Tensor.Shape) (program : CCalls.Events.Program E) (heap : Heap)
    (refs buffer : Option Address) (n m : UInt64)
    (defined : program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction shape)))
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetFloat64" (arguments none refs buffer n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (setFunction shape)
    (Runtime.modeGuard .setStart :: basicReject :: setRest shape)
    (arguments none refs buffer n m) (parameters none refs buffer n m) heap defined
    (parameters_bound true _ _ _ _ _) (by simp [setFunction, setBody, Runtime.require, List.append_assoc])
    rfl (setBody_closed shape)
  all_goals simp [parameters, CBody.bind]

end

/-! ### Consumable function contracts

These mirror the tensor Float64 accessor contracts (`TensorFloat64.GetContract`,
`SetContract`): the printed function text, its declaration closedness, its
printed-text denotation under the shared C printer, and a rejection guarantee for
a null handle. -/

section
open CTree.Printer
variable [static : StaticLiterals]
private local instance contractInterface : CInterface := cInterface static.addresses

/-- The constant-rate `fmi3GetFloat64` function contract. -/
structure GetContract (shape : Tensor.Shape) (text : String) : Prop where
  printed : text = (getFunction shape).render
  /-- Reading `der(x)` evaluates the exactly rounded rate vector through the constant
  kernel entry and returns it; the region's earlier contents do not matter. -/
  derivativeRead : ∀ {E} (program : CCalls.Events.Program E) (rates : List Rumoca.ConstantProfile.Decimal)
    (len : rates.length = shape.volume) (definitions : CLoops.Calls.Definitions)
    (backing : Heap) (pool : Address) (i : Nat) (time : Values Tensor.scalar) (state : Values shape)
    (refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode),
    CCalls.Typed.Extends definitions program.internal →
    definitions "rumoca_constant_rhs" = some (Rumoca.CConstant.rhsFunction rates) →
    (cInterface static.addresses).types "double *" = some .pointer →
    n.toNat = 1 → m.toNat = shape.volume → shape.volume < 2 ^ 64 →
    program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape)) →
    load (TensorInstance.constantStore backing pool i shape time state)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code) →
    load (TensorInstance.constantStore backing pool i shape time state)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code) →
    Reference.Allowed .get kind mode →
    load (TensorInstance.constantStore backing pool i shape time state) (refs.index 0) = some (.integer 2) →
    Writable (TensorInstance.constantStore backing pool i shape time state) buffer shape.volume →
    (∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i derivativeName).index a ≠ buffer.index b) →
    (∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling "rumoca_constant_rhs" [.pointer (some (TensorInstance.field pool i derivativeName))]
        (TensorInstance.constantStore backing pool i shape time state) .done) v →
      CCalls.Events.Resolves program v) →
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i derivativeName) (ConstantInstanceRhs.ratesVec rates shape len) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3GetFloat64" (arguments (some (TensorInstance.record pool i)) (some refs) (some buffer) n m)
          (TensorInstance.constantStore backing pool i shape time state) .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0,
          written finalHeap buffer (ConstantInstanceRhs.ratesVec rates shape len) shape.volume⟩
  closed : (getFunction shape).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text (getFunction shape)
  rejected : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (refs buffer : Option Address)
    (n m : UInt64),
    program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments none refs buffer n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

/-- The constant-rate `fmi3SetFloat64` function contract. -/
structure SetContract (shape : Tensor.Shape) (text : String) : Prop where
  printed : text = (setFunction shape).render
  closed : (setFunction shape).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text (setFunction shape)
  rejected : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (refs buffer : Option Address)
    (n m : UInt64),
    program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction shape)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetFloat64" (arguments none refs buffer n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

theorem get_contract (shape : Tensor.Shape) : GetContract shape (getFunction shape).render where
  printed := rfl
  derivativeRead program rates len definitions backing pool i time state refs buffer n m kind mode linked found
      ptrTy nref nval bounded defined hk hm allowed refRead writable separate resolves := by
    obtain ⟨finalHeap, reads, _others, ran⟩ := get_derivative_reaches program shape rates len definitions
      linked found ptrTy backing pool i time state refs buffer n m kind mode .done nref nval bounded defined
      hk hm allowed refRead writable separate resolves
    exact ⟨finalHeap, reads, fun behavior =>
      (CCalls.Events.internal_prefix program ran (CCalls.Events.return_forced program _ _)).behaviors behavior⟩
  closed := getBody_closed shape
  denotes := getFunction_denotes shape
  rejected program heap refs buffer n m defined :=
    null_get_behaviors shape program heap refs buffer n m defined

theorem set_contract (shape : Tensor.Shape) : SetContract shape (setFunction shape).render where
  printed := rfl
  closed := setBody_closed shape
  denotes := setFunction_denotes shape
  rejected program heap refs buffer n m defined :=
    null_set_behaviors shape program heap refs buffer n m defined

end

end Rumoca.FMI3.ConstantFloat64
