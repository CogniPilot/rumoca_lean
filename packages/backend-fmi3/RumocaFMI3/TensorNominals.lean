import RumocaFMI3.TensorReset
import RumocaFMI3.ErrorCalls

/-! Tensor `fmi3GetNominalsOfContinuousStates` body over the static tensor
instance record, as a package-checked product.

The scalar body assumes a single continuous state and writes the fixed nominal
`1` into `nominals[0]`. The tensor profile carries the symbolic state volume, so
this body validates the instance handle and lifecycle guard exactly as the scalar
body does (`Runtime.require` with the `getNominals` command), checks that the
requested count equals the symbolic state volume and that the caller buffer is
non-null, then writes the fixed nominal `1` into every cell of the caller buffer
with a counted `size_t` loop whose bound is the symbolic volume. No tensor
coordinate is enumerated during lowering.

The tensor adapter consumes these bodies and proofs. This module alone does
not establish source acceptance or certify an actual artifact; those obligations
belong to the composed adapter/compiler contracts. Every theorem is universal in the tensor shape, the
instance address, the caller buffer and the heap. -/
noncomputable section
namespace Rumoca.FMI3.TensorNominals
open CTree CMemory CBody CLoops
open Rumoca.CMemory.TensorView
open Rumoca.FMI3.TensorFloat64 (dstCell dstCell_lvalue run_one reject_false declare_step_e)
open Rumoca.FMI3.TensorInstance
open Binary64 (toBits)

/-- The fixed nominal fill of the caller buffer: every cell is `1`. -/
def oneValues (shape : Tensor.Shape) : Values shape := Tensor.Value.fill shape Binary64.one

/-- The nominal loop body: `dst[k] = 1;`, writing the fixed nominal into the
staged buffer cell. The integer literal `1` converts to the `1.0` binary64 value. -/
def oneBody : List Stmt := [.assign dstCell (Runtime.n 1)]

theorem oneBody_closed : oneBody.all CLoops.noDeclarations = true := by
  simp [oneBody, dstCell, CLoops.noDeclarations]

section
variable [interface : CInterface]

/-- One nominal iteration writes `1` into the buffer cell `dst[k]`. -/
theorem oneCopy_step (env : Locals) (types : Types) (heap : Heap) (regionBase : Address) {shape : Tensor.Shape}
    (i : Fin shape.volume) (old : Option Value) (rest : List Stmt)
    (dstBound : resolve env "dst" = some (.pointer (some regionBase)))
    (counter : resolve env "k" = some (.integer i.val))
    (regionStore : heap (regionBase.index i.val) = some ⟨.float64, true, old⟩) :
    CLoops.next (.running (oneBody ++ rest) env types heap) =
      some (.running rest env types
        (StateProofs.written heap (regionBase.index i.val) (toBits Binary64.one).val)) := by
  have address : CBody.lvalue env heap dstCell = some (regionBase.index i.val) :=
    dstCell_lvalue env heap regionBase i.val dstBound counter
  have rhs : CLoops.eval env types heap (Runtime.n 1) = some (.integer 1) := by
    simp [Runtime.n, CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith]
  simp only [CLoops.eval, CBody.legacyExpressions] at rhs
  simp only [dstCell] at address
  simp [oneBody, dstCell, CLoops.next, CLoops.nextWith, CBody.legacyExpressions, address, rhs, CMemory.store, regionStore, convert,
    Binary64.exactInteger_one, Value.finite, StateProofs.written]

end

section
variable [interface : CInterface]

/-- The nominal loop fills the whole caller buffer with `1`, cell by cell, in the
call scheduler. The caller supplies only the original writable buffer storage. -/
theorem oneCopy_reaches (program : CCalls.Events.Program E) (env : Locals) (types : Types)
    (heap : Heap) (regionBase : Address) {shape : Tensor.Shape}
    (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (bounded : shape.volume < 2 ^ 64) (typed : types "k" = some .size)
    (count : resolve env "expected" = some (.integer shape.volume))
    (dstBound : resolve env "dst" = some (.pointer (some regionBase)))
    (writable : Writable heap regionBase shape.volume) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (loop "k" (Runtime.v "expected") oneBody :: rest)
        (counterEnv env "k" 0) types heap) resultType stack)
      (.body (.running rest (counterEnv env "k" shape.volume) types
        (written heap regionBase (oneValues shape) shape.volume)) resultType stack) := by
  apply CCalls.Events.loop_reaches program "k" (Runtime.v "expected") oneBody rest
    (fun _ => env) types (written heap regionBase (oneValues shape)) shape.volume resultType stack typed
    bounded oneBody_closed
  · intro i inside
    simpa [Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, counterEnv, CBody.bind, resolve] using count
  · intro i inside
    obtain ⟨old, storage⟩ := Float64Calls.pending_output heap regionBase (oneValues shape) writable i inside
    have counter : resolve (counterEnv env "k" i) "k" = some (.integer i) := by
      simp [counterEnv, CBody.bind, resolve]
    have step := oneCopy_step (counterEnv env "k" i) types (written heap regionBase (oneValues shape) i)
      regionBase ⟨i, inside⟩ old
      (counterStep "k" :: loop "k" (Runtime.v "expected") oneBody :: rest)
      (by simpa [counterEnv, CBody.bind, resolve] using dstBound) counter storage
    have next : StateProofs.written (written heap regionBase (oneValues shape) i) (regionBase.index i)
        (toBits Binary64.one).val = written heap regionBase (oneValues shape) (i + 1) := by
      simp [written, dif_pos inside, StateProofs.written, Value.finite, oneValues]
    rw [next] at step
    exact .next (CCalls.Events.body_step program step resultType stack) (.refl _)

end

/-! ### The nominals body -/

def signature : Signature := ErrorCalls.nominalSignature

def arguments (handle buffer : Option Address) (count : UInt64) : List Value :=
  [.pointer handle, .pointer buffer, .integer count.toNat]

def parameters (handle buffer : Option Address) (count : UInt64) : Locals :=
  bind (bind (bind (fun _ => none) "nContinuousStates" (.integer count.toNat))
    "nominals" (.pointer buffer)) "instance" (.pointer handle)

def guardEnv (p buffer : Address) (count : UInt64) : Locals :=
  bind (parameters (some p) (some buffer) count) "m" (.pointer (some p))

/-- The request check: `nContinuousStates` must equal the state volume and the
buffer must be non-null. -/
def countReject (volume : Nat) : Stmt :=
  Runtime.reject (Runtime.any [Runtime.nev (Runtime.v "nContinuousStates") (Runtime.n volume),
    Runtime.negate (Runtime.v "nominals")]) "Invalid nominal count or pointer"

/-- The statements after the request check: stage the buffer pointer and count,
run the fill loop, and return. -/
def nominalTail (shape : Tensor.Shape) : List Stmt :=
  .declare "fmi3Float64 *" "dst" (Runtime.v "nominals") ::
  .declare "size_t" "expected" (Runtime.n shape.volume) ::
  .declare "size_t" "k" (Runtime.n 0) ::
  loop "k" (Runtime.v "expected") oneBody ::
  [Runtime.ok]

def body (shape : Tensor.Shape) : List Stmt :=
  Runtime.require .getNominals ++ (countReject shape.volume :: nominalTail shape)

def function (shape : Tensor.Shape) : CTree.Function := ⟨signature, body shape, false⟩

/-- The nominal result heap: the caller buffer is filled with the fixed nominal
`1`; every other cell is preserved. -/
def finalHeap (heap : Heap) (buffer : Address) (shape : Tensor.Shape) : Heap :=
  written heap buffer (oneValues shape) shape.volume

theorem body_closed (shape : Tensor.Shape) :
    (function shape).body.all CBodyEmbedding.closedBlocks = true := by
  simp [function, body, nominalTail, countReject, oneBody, Runtime.require, Runtime.instancePrefix,
    Runtime.modeGuard, Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, Runtime.ok,
    Runtime.v, Runtime.any, Runtime.either, Runtime.nev, Runtime.negate, dstCell,
    CBodyEmbedding.closedBlocks, CLoops.noDeclarations, CLoops.loop, CLoops.counterStep]

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem parameters_bound (handle buffer : Option Address) (count : UInt64) :
    CCalls.parameters signature.parameters (arguments handle buffer count) =
      some (parameters handle buffer count) := by
  have cc : CBody.cast "size_t" (.integer count.toNat) = some (.integer count.toNat) :=
    CLoops.Calls.cast_of_type "size_t" .size _ _ rfl (CLoops.convert_size_nat _ count.toNat_lt_size)
  simp only [signature, ErrorCalls.nominalSignature, arguments, parameters, CCalls.parameters,
    CCalls.parameterType, Bool.false_eq_true, ↓reduceIte, cc]
  rfl

/-- The request check passes for a matched non-null request. -/
theorem count_pass (heap : Heap) (p buffer : Address) (count : UInt64) (volume : Nat)
    (matched : count.toNat = volume) :
    CBody.eval (guardEnv p buffer count) heap
      (Runtime.any [Runtime.nev (Runtime.v "nContinuousStates") (Runtime.n volume),
        Runtime.negate (Runtime.v "nominals")]) = some (boolean false) := by
  simp [Runtime.any, Runtime.either, Runtime.negate, Runtime.nev, Runtime.v, Runtime.n, CBody.eval, CBody.evalWith,
    guardEnv, parameters, CBody.bind, CBody.resolve, CBody.comparison, boolean, Value.truth, matched]

/-- The staged environment at the fill loop. -/
def stagedEnv (buffer : Address) (p : Address) (shape : Tensor.Shape) (count : UInt64) : Locals :=
  bind (bind (guardEnv p buffer count) "dst" (.pointer (some buffer))) "expected" (.integer shape.volume)

def stagedTypes (types0 : Types) : Types :=
  bindType (bindType types0 "dst" .pointer) "expected" .size

section
variable (program : CCalls.Events.Program E)

/-- The complete nominals body: it fills the caller buffer with the fixed nominal
`1` and changes no other cell. -/
theorem nominal_reaches (shape : Tensor.Shape) (heap : Heap) (p buffer : Address) (count : UInt64)
    (kind : Kind) (mode : Mode) (stack : CCalls.Typed.Continuation)
    (matched : count.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetNominalsOfContinuousStates" =
      some (.tree (function shape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getNominals kind mode)
    (writable : Writable heap buffer shape.volume) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling "fmi3GetNominalsOfContinuousStates" (arguments (some p) (some buffer) count) heap stack)
      (.returning (.integer 0) (finalHeap heap buffer shape) stack) := by
  have accepted := LifecycleGuard.accept (parameters (some p) (some buffer) count) heap p
    .getNominals kind mode (countReject shape.volume :: nominalTail shape)
    (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hm allowed
  have prefix_run : CBody.run 4 (.running (body shape) (parameters (some p) (some buffer) count) heap) =
      some (.running (nominalTail shape) (guardEnv p buffer count) heap) := by
    rw [body, show (4 : Nat) = 3 + 1 from rfl, CBody.run_add, accepted, Option.bind_some]
    exact run_one (reject_false (guardEnv p buffer count) heap _
      "Invalid nominal count or pointer" (nominalTail shape)
      (count_pass heap p buffer count _ matched))
  obtain ⟨types0, entered⟩ := CCalls.Events.body_prefix_reaches program (function shape)
    (arguments (some p) (some buffer) count) (parameters (some p) (some buffer) count)
    (guardEnv p buffer count) heap heap (nominalTail shape) stack 4 defined
    (parameters_bound _ _ _) (body_closed shape) prefix_run
  refine entered.trans ?_
  have mBound : guardEnv p buffer count "m" = some (.pointer (some p)) := by
    simp [guardEnv, CBody.bind]
  -- stage `dst`, `expected`
  have s_dst : CLoops.next (.running (nominalTail shape) (guardEnv p buffer count) types0 heap) =
      some (.running (.declare "size_t" "expected" (Runtime.n shape.volume) ::
        .declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") oneBody :: [Runtime.ok])
        (bind (guardEnv p buffer count) "dst" (.pointer (some buffer)))
        (bindType types0 "dst" .pointer) heap) :=
    declare_step_e (guardEnv p buffer count) types0 heap "fmi3Float64 *" "dst"
      (Runtime.v "nominals") .pointer (.pointer (some buffer)) (.pointer (some buffer)) _
      (by simp [guardEnv, parameters, CBody.bind]) rfl
      (by simp [Runtime.v, CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith, guardEnv, parameters, CBody.bind, CBody.resolve]) rfl
  have s_exp : CLoops.next (.running (.declare "size_t" "expected" (Runtime.n shape.volume) ::
        .declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") oneBody :: [Runtime.ok])
        (bind (guardEnv p buffer count) "dst" (.pointer (some buffer)))
        (bindType types0 "dst" .pointer) heap) =
      some (.running (.declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") oneBody ::
        [Runtime.ok]) (stagedEnv buffer p shape count) (stagedTypes types0) heap) :=
    declare_step_e _ _ heap "size_t" "expected" (Runtime.n shape.volume) .size
      (.integer shape.volume) (.integer shape.volume) _ (by simp [guardEnv, parameters, CBody.bind])
      rfl (by simp [Runtime.n, CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith]) (CLoops.convert_size_nat _ bounded)
  refine .next (CCalls.Events.body_step program s_dst "fmi3Status" stack)
    (.next (CCalls.Events.body_step program s_exp "fmi3Status" stack) ?_)
  set env := stagedEnv buffer p shape count with henv
  have fresh_k : env "k" = none := by simp [henv, stagedEnv, guardEnv, parameters, CBody.bind]
  have expBound : resolve env "expected" = some (.integer shape.volume) := by
    simp [henv, stagedEnv, CBody.bind, CBody.resolve]
  have dstBound : resolve env "dst" = some (.pointer (some buffer)) := by
    simp [henv, stagedEnv, CBody.bind, CBody.resolve]
  have fmiok : env "fmi3OK" = none := by simp [henv, stagedEnv, guardEnv, parameters, CBody.bind]
  refine .next (CCalls.Events.body_step program
    (CLoops.counter_initialize env (stagedTypes types0) heap "k"
      (loop "k" (Runtime.v "expected") oneBody :: [Runtime.ok]) fresh_k rfl) _ stack) ?_
  refine (oneCopy_reaches program env (CLoops.bindType (stagedTypes types0) "k" .size) heap
    buffer [Runtime.ok] _ stack bounded (by simp [CLoops.bindType]) expBound dstBound writable).trans ?_
  exact DerivativeCalls.finish program _ (counterEnv env "k" shape.volume)
    (CLoops.bindType (stagedTypes types0) "k" .size) stack (by simp [counterEnv, CBody.bind, fmiok])

theorem nominal_behaviors (shape : Tensor.Shape) (heap : Heap) (p buffer : Address) (count : UInt64)
    (kind : Kind) (mode : Mode)
    (matched : count.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetNominalsOfContinuousStates" =
      some (.tree (function shape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getNominals kind mode)
    (writable : Writable heap buffer shape.volume) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetNominalsOfContinuousStates" (arguments (some p) (some buffer) count) heap .done)
      behavior ↔
      behavior = .terminates [] ⟨.integer 0, finalHeap heap buffer shape⟩ :=
  (CCalls.Events.internal_prefix program (nominal_reaches program shape heap p buffer count kind mode
    .done matched bounded defined hk hm allowed writable)
    (CCalls.Events.return_forced program _ _)).behaviors behavior

theorem null_behaviors (shape : Tensor.Shape) (heap : Heap) (buffer : Option Address) (count : UInt64)
    (defined : program.internal.definitions "fmi3GetNominalsOfContinuousStates" =
      some (.tree (function shape))) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetNominalsOfContinuousStates" (arguments none buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (function shape)
    (Runtime.modeGuard .getNominals :: countReject shape.volume :: nominalTail shape)
    (arguments none buffer count) (parameters none buffer count) heap defined (parameters_bound _ _ _)
    (by simp [function, body, Runtime.require, List.append_assoc]) rfl (body_closed shape)
  all_goals simp [parameters, CBody.bind]

/-- The filled caller buffer reads the fixed nominal `1` in every cell. -/
theorem reads_nominals (shape : Tensor.Shape) (heap : Heap) (buffer : Address) :
    Reads (finalHeap heap buffer shape) buffer (oneValues shape) := by
  intro i
  have cell : finalHeap heap buffer shape (buffer.index i.val) =
      some ⟨.float64, true, some (.finite (oneValues shape)[i])⟩ := by
    have := written_at heap buffer (oneValues shape) shape.volume (le_refl _) i
    simpa [finalHeap, i.isLt] using this
  simp [load, cell, convert, Value.finite]

end
end

/-! ### Framing across instances -/

/-- The successful nominals write into a caller buffer separated from a pool
instance preserves every tensor cell of that instance. -/
theorem preserves_instance (heap : Heap) (buffer : Address) (shape : Tensor.Shape)
    (q : Address) (outside : ∀ i < shape.volume, q ≠ buffer.index i) :
    finalHeap heap buffer shape q = heap q := by
  simpa [finalHeap] using written_frame heap buffer (oneValues shape) shape.volume q outside

/-! ### Printed text and denotation -/

section
open CTree.Printer CTree.Syntax

theorem signature_printable : SignaturePrintable RuntimePrinter.typedefs signature := by
  refine ⟨.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel, ?_⟩
  intro param member
  simp only [signature, ErrorCalls.nominalSignature, List.mem_cons, List.not_mem_nil, or_false]
    at member
  rcases member with rfl | rfl | rfl <;>
    refine ⟨.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩

theorem body_printable (shape : Tensor.Shape) :
    ∀ stmt ∈ (function shape).body, ItemPrintable RuntimePrinter.typedefs stmt := by
  have iType : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
    .pointer (text := "Instance") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have fType : TypeSpelling RuntimePrinter.typedefs "fmi3Float64 *" :=
    .pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have sType : TypeSpelling RuntimePrinter.typedefs "size_t" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  simp only [function, body, nominalTail, countReject, oneBody, dstCell, Runtime.require,
      Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression, permittedModes,
      Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, Runtime.ok, Runtime.field, Runtime.v,
      Runtime.n, Runtime.eqv, Runtime.nev, Runtime.both, Runtime.either, Runtime.negate, Runtime.any,
      Runtime.mode, Runtime.call, CLoops.loop, CLoops.counterStep, List.foldr_cons, List.foldr_nil,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and,
      List.cons_append, List.nil_append, forall_eq] <;>
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
      | apply Printable.dereference
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

theorem function_denotes (shape : Tensor.Shape) :
    FunctionDenotes RuntimePrinter.typedefs (function shape).render (function shape) :=
  CTree.Printer.function_denotes ⟨signature_printable, body_printable shape⟩

end

/-! ### The nominals contract -/

section
open CTree.Printer
variable [static : StaticLiterals]
private local instance contractInterface : CInterface := cInterface static.addresses

/-- The tensor `fmi3GetNominalsOfContinuousStates` function contract. -/
structure Contract (shape : Tensor.Shape) (text : String) : Prop where
  printed : text = (function shape).render
  closed : (function shape).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text (function shape)
  successful : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (p buffer : Address)
    (count : UInt64) (kind : Kind) (mode : Mode),
    count.toNat = shape.volume →
    shape.volume < 2 ^ 64 →
    program.internal.definitions "fmi3GetNominalsOfContinuousStates" = some (.tree (function shape)) →
    load heap (p.member "kind") = some (.integer kind.code) →
    load heap (p.member "mode") = some (.integer mode.code) →
    Reference.Allowed .getNominals kind mode →
    Writable heap buffer shape.volume →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetNominalsOfContinuousStates" (arguments (some p) (some buffer) count) heap .done)
      behavior ↔
      behavior = .terminates [] ⟨.integer 0, finalHeap heap buffer shape⟩
  nominals : ∀ heap buffer, Reads (finalHeap heap buffer shape) buffer (oneValues shape)
  null : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (buffer : Option Address) (count : UInt64),
    program.internal.definitions "fmi3GetNominalsOfContinuousStates" = some (.tree (function shape)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetNominalsOfContinuousStates" (arguments none buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

theorem contract (shape : Tensor.Shape) : Contract shape (function shape).render where
  printed := rfl
  closed := body_closed shape
  denotes := function_denotes shape
  successful program heap p buffer count kind mode matched bounded defined hk hm allowed writable :=
    nominal_behaviors program shape heap p buffer count kind mode matched bounded defined hk hm allowed
      writable
  nominals heap buffer := reads_nominals shape heap buffer
  null program heap buffer count defined := null_behaviors program shape heap buffer count defined

end

end Rumoca.FMI3.TensorNominals
