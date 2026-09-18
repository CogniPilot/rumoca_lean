import RumocaFMI3.TensorFloat64Access

/-! Constant-rate `fmi3GetFloat64` / `fmi3SetFloat64` bodies over the static
constant-rate instance record, as package-checked products.

The constant-rate profile (`G01`) exposes no input tensor and no dense output.
Its value references are renumbered without the input: `0` the independent time
base (element count 1), `1` the state vector `x`, `2` the state derivative
`der(x)` (each element count `shape.volume`). The getter denotes any of the
three references; the setter admits only the state reference `1` (writable) and
rejects the derivative reference `2` as read-only, matching the constant-rate
model description (`TensorMetadata.constantModelDescription`, `1` state, `2`
derivative). The shared request-check, staging, copy-loop and finiteness
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
open Rumoca.FMI3.TensorFloat64 (vr0 getArm memberPointer getLoopSuffix basicReject countReject
  setArm setLoopSuffix validateBody getCopyBody setCopyBody srcCell dstCell)
open Rumoca.FMI3.Float64Calls (signature parameters arguments parameters_bound output)

/-! ### The getter body -/

/-- Dispatch tail for reference 2 (the derivative `der(x)`). -/
def getDispatch2 (shape : Tensor.Shape) : List Stmt :=
  [Runtime.branch (Runtime.eqv vr0 (Runtime.n 2)) (getArm derivativeName shape.volume)
    [Runtime.fail "Unknown value reference"]]

/-- Dispatch tail for references 1 and above (the state `x`). -/
def getDispatch1 (shape : Tensor.Shape) : List Stmt :=
  [Runtime.branch (Runtime.eqv vr0 (Runtime.n 1)) (getArm stateName shape.volume)
    (getDispatch2 shape)]

/-- Dispatch one value reference to its region, staging its pointer and count:
`0` time (count 1), `1` state, `2` derivative; every other reference fails. -/
def getDispatch (shape : Tensor.Shape) : Stmt :=
  Runtime.branch (Runtime.eqv vr0 (Runtime.n 0)) (getArm timeName 1) (getDispatch1 shape)

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
    getLoopSuffix, getArm, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject,
    Runtime.branch, Runtime.fail, Runtime.ret, Runtime.ok, getCopyBody, CBodyEmbedding.closedBlocks,
    CLoops.noDeclarations, CLoops.loop, CLoops.counterStep]

/-! ### The setter body -/

/-- The constant-rate setter dispatch: only the state `x` (reference `1`) is
writable. The time base and derivative are read-only, so every other reference
fails. -/
def setDispatch (shape : Tensor.Shape) : Stmt :=
  Runtime.branch (Runtime.eqv vr0 (Runtime.n 1)) (setArm stateName shape.volume)
    [Runtime.fail "Unknown or read-only value reference"]

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

set_option maxHeartbeats 4000000 in
/-- Every statement of the getter body prints its intended C token grammar. -/
theorem getBody_printable (shape : Tensor.Shape) :
    ∀ stmt ∈ (getFunction shape).body, ItemPrintable RuntimePrinter.typedefs stmt := by
  have iType : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
    .pointer (text := "Instance") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have fType : TypeSpelling RuntimePrinter.typedefs "fmi3Float64 *" :=
    .pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have sType : TypeSpelling RuntimePrinter.typedefs "size_t" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  simp only [getFunction, getBody, getRest, getDispatch, getDispatch1, getDispatch2, getArm,
      getLoopSuffix, memberPointer, Runtime.region, timeName, stateName, inputName, derivativeName,
      outputName, basicReject, countReject, vr0, Runtime.require, Runtime.instancePrefix,
      Runtime.modeGuard, Runtime.allowedExpression, permittedModes, Runtime.reject, Runtime.branch,
      Runtime.fail, Runtime.ret, Runtime.ok, Runtime.field, Runtime.v, Runtime.n, Runtime.eqv,
      Runtime.nev, Runtime.both, Runtime.either, Runtime.negate, Runtime.any, Runtime.mode, Runtime.lt,
      Runtime.call, getCopyBody, srcCell, output, CLoops.loop, CLoops.counterStep, List.foldr_cons,
      List.foldr_nil, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      List.forall_mem_nil, or_false, or_imp, forall_and, List.cons_append, List.nil_append, forall_eq] <;>
    repeat first
      | exact CNull.literal_printable _
      | exact iType
      | exact fType
      | exact sType
      | apply And.intro
      | apply ItemPrintable.declare
      | apply ItemPrintable.assign
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

set_option maxHeartbeats 4000000 in
/-- Every statement of the setter body prints its intended C token grammar. -/
theorem setBody_printable (shape : Tensor.Shape) :
    ∀ stmt ∈ (setFunction shape).body, ItemPrintable RuntimePrinter.typedefs stmt := by
  have iType : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
    .pointer (text := "Instance") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have fType : TypeSpelling RuntimePrinter.typedefs "fmi3Float64 *" :=
    .pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have sType : TypeSpelling RuntimePrinter.typedefs "size_t" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  simp only [setFunction, setBody, setRest, setDispatch, setArm, setLoopSuffix, validateBody,
      memberPointer, Runtime.region, timeName, stateName, inputName, derivativeName, outputName,
      basicReject, countReject, vr0, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard,
      Runtime.allowedExpression, permittedModes, Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret,
      Runtime.ok, Runtime.field, Runtime.v, Runtime.n, Runtime.eqv, Runtime.nev, Runtime.both, Runtime.either,
      Runtime.negate, Runtime.any, Runtime.mode, Runtime.lt, Runtime.call, Runtime.finite, setCopyBody,
      dstCell, output, CLoops.loop, CLoops.counterStep, List.foldr_cons, List.foldr_nil, List.map_cons,
      List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, List.forall_mem_nil, or_false, or_imp,
      forall_and, List.cons_append, List.nil_append, forall_eq] <;>
    repeat first
      | exact CNull.literal_printable _
      | exact iType
      | exact fType
      | exact sType
      | apply And.intro
      | apply ItemPrintable.declare
      | apply ItemPrintable.assign
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

/-- The rendered getter denotes its function under the shared C printer. -/
theorem getFunction_denotes (shape : Tensor.Shape) :
    FunctionDenotes RuntimePrinter.typedefs (getFunction shape).render (getFunction shape) :=
  CTree.Printer.function_denotes ⟨TensorFloat64.signature_printable false, getBody_printable shape⟩

/-- The rendered setter denotes its function under the shared C printer. -/
theorem setFunction_denotes (shape : Tensor.Shape) :
    FunctionDenotes RuntimePrinter.typedefs (setFunction shape).render (setFunction shape) :=
  CTree.Printer.function_denotes ⟨TensorFloat64.signature_printable true, setBody_printable shape⟩

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
