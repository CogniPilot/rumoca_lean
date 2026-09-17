import RumocaFMI3.TensorSetTime

/-! Tensor `fmi3Reset` body over the static tensor instance record, as a
package-checked product.

The body validates the instance handle and lifecycle guard exactly as the scalar
body does (`Runtime.require` with the `reset` command), then restores the fixed-zero
initialization of the prepared IVP: a counted `size_t` loop whose bound is the
symbolic state volume writes zero into every cell of the state region `x`, and the
independent time base is reset to zero. The loop bound is the symbolic volume, so
no tensor coordinate is enumerated. The post-reset state region reads the same
value as the prepared initialization program `fill shape .zero` of the admitted
kernel.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and the scalar adapter, `Runtime.lean` and every existing
contract are unchanged. Every theorem is universal in the tensor shape, the
instance address (and, for the framing corollary, the instance index of the static
pool) and the heap. -/
noncomputable section
namespace Rumoca.FMI3.TensorReset
open CTree CMemory CBody CLoops
open Rumoca.CMemory.TensorView
open Rumoca.FMI3.TensorFloat64 (dstCell dstCell_lvalue run_one reject_false declare_step_e)
open Rumoca.FMI3.TensorInstance
open Binary64 (toBits)

/-- The fixed-zero fill of the state region: every cell is `+0`. -/
def zeroValues (shape : Tensor.Shape) : Values shape := Tensor.Value.fill shape Binary64.positiveZero

/-- The reset loop body: `dst[k] = 0;`, writing `+0` into the staged region cell.
The integer literal `0` converts to the `+0` binary64 value. -/
def zeroBody : List Stmt := [.assign dstCell (Runtime.n 0)]

theorem zeroBody_closed : zeroBody.all CLoops.noDeclarations = true := by
  simp [zeroBody, dstCell, CLoops.noDeclarations]

section
variable [interface : CInterface]

/-- One reset iteration writes `+0` into the region cell `dst[k]`. -/
theorem zeroCopy_step (env : Locals) (types : Types) (heap : Heap) (regionBase : Address) {shape : Tensor.Shape}
    (i : Fin shape.volume) (old : Option Value) (rest : List Stmt)
    (dstBound : resolve env "dst" = some (.pointer (some regionBase)))
    (counter : resolve env "k" = some (.integer i.val))
    (regionStore : heap (regionBase.index i.val) = some ⟨.float64, true, old⟩) :
    CLoops.next (.running (zeroBody ++ rest) env types heap) =
      some (.running rest env types
        (StateProofs.written heap (regionBase.index i.val) (toBits Binary64.positiveZero).val)) := by
  have address : CBody.lvalue env heap dstCell = some (regionBase.index i.val) :=
    dstCell_lvalue env heap regionBase i.val dstBound counter
  have rhs : CLoops.eval env types heap (Runtime.n 0) = some (.integer 0) := by
    simp [Runtime.n, CLoops.eval, CBody.eval]
  simp only [dstCell] at address
  simp [zeroBody, dstCell, CLoops.next, address, rhs, CMemory.store, regionStore, convert,
    Binary64.exactInteger_zero, Value.finite, StateProofs.written]

end

section
variable [interface : CInterface]

/-- The reset loop fills the whole region with `+0`, cell by cell, in the call
scheduler. The caller supplies only the original writable region storage. -/
theorem zeroCopy_reaches (program : CCalls.Events.Program E) (env : Locals) (types : Types)
    (heap : Heap) (regionBase : Address) {shape : Tensor.Shape}
    (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (bounded : shape.volume < 2 ^ 64) (typed : types "k" = some .size)
    (count : resolve env "expected" = some (.integer shape.volume))
    (dstBound : resolve env "dst" = some (.pointer (some regionBase)))
    (writable : Writable heap regionBase shape.volume) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (loop "k" (Runtime.v "expected") zeroBody :: rest)
        (counterEnv env "k" 0) types heap) resultType stack)
      (.body (.running rest (counterEnv env "k" shape.volume) types
        (written heap regionBase (zeroValues shape) shape.volume)) resultType stack) := by
  apply CCalls.Events.loop_reaches program "k" (Runtime.v "expected") zeroBody rest
    (fun _ => env) types (written heap regionBase (zeroValues shape)) shape.volume resultType stack typed
    bounded zeroBody_closed
  · intro i inside
    simpa [Runtime.v, CBody.eval, counterEnv, CBody.bind, resolve] using count
  · intro i inside
    obtain ⟨old, storage⟩ := Float64Calls.pending_output heap regionBase (zeroValues shape) writable i inside
    have counter : resolve (counterEnv env "k" i) "k" = some (.integer i) := by
      simp [counterEnv, CBody.bind, resolve]
    have step := zeroCopy_step (counterEnv env "k" i) types (written heap regionBase (zeroValues shape) i)
      regionBase ⟨i, inside⟩ old
      (counterStep "k" :: loop "k" (Runtime.v "expected") zeroBody :: rest)
      (by simpa [counterEnv, CBody.bind, resolve] using dstBound) counter storage
    have next : StateProofs.written (written heap regionBase (zeroValues shape) i) (regionBase.index i)
        (toBits Binary64.positiveZero).val = written heap regionBase (zeroValues shape) (i + 1) := by
      simp [written, dif_pos inside, StateProofs.written, Value.finite, zeroValues]
    rw [next] at step
    exact .next (CCalls.Events.body_step program step resultType stack) (.refl _)

end

/-! ### The reset body -/

def signature : Signature :=
  ⟨"fmi3Status", "fmi3Reset", [⟨"fmi3Instance", "instance", false⟩]⟩

def arguments (handle : Option Address) : List Value := [.pointer handle]

def parameters (handle : Option Address) : Locals := bind (fun _ => none) "instance" (.pointer handle)

def guardEnv (p : Address) : Locals := bind (parameters (some p)) "m" (.pointer (some p))

/-- The statements after the guard: stage the region pointer and count, run the
zero-fill loop, reset the time base, and return. -/
def resetTail (shape : Tensor.Shape) : List Stmt :=
  .declare "fmi3Float64 *" "dst" (.address (Runtime.field stateName)) ::
  .declare "size_t" "expected" (Runtime.n shape.volume) ::
  .declare "size_t" "k" (Runtime.n 0) ::
  loop "k" (Runtime.v "expected") zeroBody ::
  Runtime.put "time" (Runtime.n 0) :: [Runtime.ok]

def body (shape : Tensor.Shape) : List Stmt := Runtime.require .reset ++ resetTail shape

def function (shape : Tensor.Shape) : CTree.Function := ⟨signature, body shape, false⟩

/-- The reset result heap: exactly the state region of instance `p` is `+0`-filled
and the time cell is `+0`; every other cell is preserved. -/
def finalHeap (heap : Heap) (p : Address) (shape : Tensor.Shape) : Heap :=
  replace (written heap (p.member stateName) (zeroValues shape) shape.volume)
    (p.member "time") ⟨.float64, true, some (.finite Binary64.positiveZero)⟩

theorem body_closed (shape : Tensor.Shape) :
    (function shape).body.all CBodyEmbedding.closedBlocks = true := by
  simp [function, body, resetTail, zeroBody, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard,
    Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, Runtime.ok, Runtime.put, Runtime.field,
    Runtime.v, dstCell, CBodyEmbedding.closedBlocks, CLoops.noDeclarations, CLoops.loop,
    CLoops.counterStep]

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem parameters_bound (handle : Option Address) :
    CCalls.parameters signature.parameters (arguments handle) = some (parameters handle) := rfl

/-- The staged environment at the zero-fill loop. -/
def stagedEnv (p : Address) (shape : Tensor.Shape) : Locals :=
  bind (bind (guardEnv p) "dst" (.pointer (some (p.member stateName)))) "expected" (.integer shape.volume)

def stagedTypes (types0 : Types) : Types :=
  bindType (bindType types0 "dst" .pointer) "expected" .size

section
variable (program : CCalls.Events.Program E)

/-- The complete reset: it fills the instance state region with `+0`, resets the
time base to `+0`, and changes no other cell. -/
theorem reset_reaches (shape : Tensor.Shape) (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (timeOld : Option Value) (stack : CCalls.Typed.Continuation) (bounded : shape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3Reset" = some (.tree (function shape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .reset kind mode)
    (writable : Writable heap (p.member stateName) shape.volume)
    (timeCell : heap (p.member "time") = some ⟨.float64, true, timeOld⟩)
    (separate : ∀ a < shape.volume, (p.member stateName).index a ≠ p.member "time") :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling "fmi3Reset" (arguments (some p)) heap stack)
      (.returning (.integer 0) (finalHeap heap p shape) stack) := by
  have accepted : CBody.run 3 (.running (body shape) (parameters (some p)) heap) =
      some (.running (resetTail shape) (guardEnv p) heap) := by
    rw [body]
    exact LifecycleGuard.accept (parameters (some p)) heap p .reset kind mode (resetTail shape)
      (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hm allowed
  obtain ⟨types0, entered⟩ := CCalls.Events.body_prefix_reaches program (function shape)
    (arguments (some p)) (parameters (some p)) (guardEnv p) heap heap (resetTail shape) stack 3 defined
    (parameters_bound _) (body_closed shape) accepted
  refine entered.trans ?_
  have mBound : guardEnv p "m" = some (.pointer (some p)) := by simp [guardEnv, CBody.bind]
  -- stage `dst`, `expected`
  have s_dst : CLoops.next (.running (resetTail shape) (guardEnv p) types0 heap) =
      some (.running (.declare "size_t" "expected" (Runtime.n shape.volume) ::
        .declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") zeroBody ::
        Runtime.put "time" (Runtime.n 0) :: [Runtime.ok])
        (bind (guardEnv p) "dst" (.pointer (some (p.member stateName)))) (bindType types0 "dst" .pointer) heap) :=
    declare_step_e (guardEnv p) types0 heap "fmi3Float64 *" "dst"
      (.address (Runtime.field stateName)) .pointer (.pointer (some (p.member stateName)))
      (.pointer (some (p.member stateName))) _ (by simp [guardEnv, parameters, CBody.bind]) rfl
      (by apply CBodyEmbedding.eval_refines
          simp [Runtime.field, Runtime.v, CBody.eval, CBody.lvalue, guardEnv, parameters, CBody.bind,
            CBody.resolve, mBound, Value.address]) rfl
  have s_exp : CLoops.next (.running (.declare "size_t" "expected" (Runtime.n shape.volume) ::
        .declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") zeroBody ::
        Runtime.put "time" (Runtime.n 0) :: [Runtime.ok])
        (bind (guardEnv p) "dst" (.pointer (some (p.member stateName)))) (bindType types0 "dst" .pointer) heap) =
      some (.running (.declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") zeroBody ::
        Runtime.put "time" (Runtime.n 0) :: [Runtime.ok]) (stagedEnv p shape) (stagedTypes types0) heap) :=
    declare_step_e _ _ heap "size_t" "expected" (Runtime.n shape.volume) .size
      (.integer shape.volume) (.integer shape.volume) _ (by simp [guardEnv, parameters, CBody.bind])
      rfl (by simp [Runtime.n, CLoops.eval, CBody.eval]) (CLoops.convert_size_nat _ bounded)
  refine .next (CCalls.Events.body_step program s_dst "fmi3Status" stack)
    (.next (CCalls.Events.body_step program s_exp "fmi3Status" stack) ?_)
  set env := stagedEnv p shape with henv
  have fresh_k : env "k" = none := by simp [henv, stagedEnv, guardEnv, parameters, CBody.bind]
  have expBound : resolve env "expected" = some (.integer shape.volume) := by
    simp [henv, stagedEnv, CBody.bind, CBody.resolve]
  have dstBound : resolve env "dst" = some (.pointer (some (p.member stateName))) := by
    simp [henv, stagedEnv, guardEnv, parameters, CBody.bind, CBody.resolve]
  have fmiok : env "fmi3OK" = none := by simp [henv, stagedEnv, guardEnv, parameters, CBody.bind]
  have mBound' : resolve env "m" = some (.pointer (some p)) := by
    simp [henv, stagedEnv, guardEnv, parameters, CBody.bind, CBody.resolve]
  -- initialize the counter, run the zero-fill loop
  refine .next (CCalls.Events.body_step program
    (CLoops.counter_initialize env (stagedTypes types0) heap "k"
      (loop "k" (Runtime.v "expected") zeroBody :: Runtime.put "time" (Runtime.n 0) :: [Runtime.ok])
      fresh_k rfl) _ stack) ?_
  refine (zeroCopy_reaches program env (CLoops.bindType (stagedTypes types0) "k" .size) heap
    (p.member stateName) (Runtime.put "time" (Runtime.n 0) :: [Runtime.ok]) _ stack bounded
    (by simp [CLoops.bindType]) expBound dstBound writable).trans ?_
  -- the time reset, then return
  set filled := written heap (p.member stateName) (zeroValues shape) shape.volume with hfilled
  have timeStore : filled (p.member "time") = some ⟨.float64, true, timeOld⟩ := by
    rw [hfilled, written_frame heap (p.member stateName) (zeroValues shape) shape.volume (p.member "time")
      (fun a ha => (separate a ha).symm)]
    exact timeCell
  have timeResolve : resolve (counterEnv env "k" shape.volume) "m" = some (.pointer (some p)) := by
    simpa [counterEnv, CBody.bind, resolve] using mBound'
  have s_time : CLoops.next (.running (Runtime.put "time" (Runtime.n 0) :: [Runtime.ok])
      (counterEnv env "k" shape.volume) (CLoops.bindType (stagedTypes types0) "k" .size) filled) =
      some (.running [Runtime.ok] (counterEnv env "k" shape.volume)
        (CLoops.bindType (stagedTypes types0) "k" .size) (finalHeap heap p shape)) := by
    have hconv : convert .float64 (.integer 0) = some (.finite Binary64.positiveZero) := by
      simp [convert, Binary64.exactInteger_zero, Option.map_some]
    have hstore : CMemory.store filled (p.member "time") (.integer 0) =
        some (finalHeap heap p shape) := by
      rw [finalHeap, ← hfilled]
      exact store_of_convert filled (p.member "time") timeOld (.integer 0)
        (.finite Binary64.positiveZero) .float64 (by decide) timeStore hconv
    simp [Runtime.put, Runtime.field, Runtime.v, Runtime.n, CLoops.next, CLoops.eval, CBody.eval,
      CBody.lvalue, timeResolve, Value.address, hstore]
  refine .next (CCalls.Events.body_step program s_time "fmi3Status" stack) ?_
  exact DerivativeCalls.finish program _ (counterEnv env "k" shape.volume)
    (CLoops.bindType (stagedTypes types0) "k" .size) stack (by simp [counterEnv, CBody.bind, fmiok])

theorem reset_behaviors (shape : Tensor.Shape) (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (timeOld : Option Value) (bounded : shape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3Reset" = some (.tree (function shape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .reset kind mode)
    (writable : Writable heap (p.member stateName) shape.volume)
    (timeCell : heap (p.member "time") = some ⟨.float64, true, timeOld⟩)
    (separate : ∀ a < shape.volume, (p.member stateName).index a ≠ p.member "time") (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3Reset" (arguments (some p)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, finalHeap heap p shape⟩ :=
  (CCalls.Events.internal_prefix program (reset_reaches program shape heap p kind mode timeOld .done
    bounded defined hk hm allowed writable timeCell separate)
    (CCalls.Events.return_forced program _ _)).behaviors behavior

theorem null_behaviors (shape : Tensor.Shape) (heap : Heap)
    (defined : program.internal.definitions "fmi3Reset" = some (.tree (function shape))) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3Reset" (arguments none) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (function shape)
    (Runtime.modeGuard .reset :: resetTail shape)
    (arguments none) (parameters none) heap defined (parameters_bound _)
    (by simp [function, body, Runtime.require, List.append_assoc]) rfl (body_closed shape)
  all_goals simp [parameters, CBody.bind]

/-- The post-reset state region reads the prepared initialization program's value:
`fill shape .zero`, i.e. the fixed-zero fill. -/
theorem reads_initialization (shape : Tensor.Shape) (heap : Heap) (p : Address) :
    Reads (finalHeap heap p shape) (p.member stateName) (zeroValues shape) := by
  intro i
  have distinct : (p.member stateName).index i.val ≠ p.member "time" := by
    have hne : stateName ≠ "time" := by decide +kernel
    intro h
    exact absurd (congrArg Address.members h) (by
      simp [Address.index, Address.member, hne])
  have frame : written heap (p.member stateName) (zeroValues shape) shape.volume
      ((p.member stateName).index i.val) = some ⟨.float64, true, some (.finite (zeroValues shape)[i])⟩ := by
    have := written_at heap (p.member stateName) (zeroValues shape) shape.volume (le_refl _) i
    simpa [i.isLt] using this
  have cell : finalHeap heap p shape ((p.member stateName).index i.val) =
      some ⟨.float64, true, some (.finite (zeroValues shape)[i])⟩ := by
    rw [finalHeap, replace_other _ _ _ _ distinct]; exact frame
  simp [load, cell, convert, Value.finite]

/-- The prepared IVP initialization program of the admitted kernel evaluates to
the fixed-zero fill that reset restores. -/
theorem initialization_is_zero (shape : Tensor.Shape)
    (ops : Tensor.ScalarOps Binary64.Value) (one : Binary64.Value) :
    (TensorInstanceRhs.kernel shape).problem.initial ops Binary64.positiveZero one =
      zeroValues shape := rfl

end
end

/-! ### Framing across instances -/

/-- The successful reset of instance `i` preserves every tensor cell of every
other instance of the static pool. -/
theorem preserves_other_instances (heap : Heap) (pool : Address) (i j : Nat) (shape : Tensor.Shape)
    (b : String) (k : Nat) (different : j ≠ i) :
    finalHeap heap (TensorInstance.record pool i) shape ((TensorInstance.field pool j b).index k) =
      heap ((TensorInstance.field pool j b).index k) := by
  have time_ne : (TensorInstance.field pool j b).index k ≠ (TensorInstance.record pool i).member "time" := by
    have sep := Address.instances_separate pool j i different b timeName k 0
    simpa [TensorInstance.field, TensorInstance.record] using sep
  have state_ne : ∀ a < shape.volume,
      (TensorInstance.field pool j b).index k ≠ ((TensorInstance.record pool i).member stateName).index a := by
    intro a _
    have sep := Address.instances_separate pool j i different b stateName k a
    simpa [TensorInstance.field, TensorInstance.record] using sep
  rw [finalHeap, replace_other _ _ _ _ time_ne,
    written_frame heap _ (zeroValues shape) shape.volume _ (fun a ha => state_ne a ha)]

/-! ### Printed text and denotation -/

section
open CTree.Printer CTree.Syntax

theorem signature_printable : SignaturePrintable RuntimePrinter.typedefs signature := by
  refine ⟨.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel, ?_⟩
  intro param member
  simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  exact ⟨.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩

theorem body_printable (shape : Tensor.Shape) :
    ∀ stmt ∈ (function shape).body, ItemPrintable RuntimePrinter.typedefs stmt := by
  have iType : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
    .pointer (text := "Instance") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have fType : TypeSpelling RuntimePrinter.typedefs "fmi3Float64 *" :=
    .pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have sType : TypeSpelling RuntimePrinter.typedefs "size_t" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  simp only [function, body, resetTail, zeroBody, dstCell, Runtime.require, Runtime.instancePrefix,
      Runtime.modeGuard, Runtime.allowedExpression, permittedModes, Runtime.reject, Runtime.branch,
      Runtime.fail, Runtime.ret, Runtime.ok, Runtime.put, Runtime.field, Runtime.v, Runtime.n,
      Runtime.eqv, Runtime.both, Runtime.either, Runtime.negate, Runtime.any, Runtime.mode, Runtime.call,
      CLoops.loop, CLoops.counterStep, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, List.cons_append, List.nil_append,
      forall_eq] <;>
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

/-! ### The reset contract -/

section
open CTree.Printer
variable [static : StaticLiterals]
private local instance contractInterface : CInterface := cInterface static.addresses

/-- The tensor `fmi3Reset` function contract, mirroring the scalar
`Reset.FunctionContract` shape. -/
structure Contract (shape : Tensor.Shape) (text : String) : Prop where
  printed : text = (function shape).render
  closed : (function shape).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text (function shape)
  successful : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
    (kind : Kind) (mode : Mode) (timeOld : Option Value),
    shape.volume < 2 ^ 64 →
    program.internal.definitions "fmi3Reset" = some (.tree (function shape)) →
    load heap (p.member "kind") = some (.integer kind.code) →
    load heap (p.member "mode") = some (.integer mode.code) →
    Reference.Allowed .reset kind mode →
    Writable heap (p.member stateName) shape.volume →
    heap (p.member "time") = some ⟨.float64, true, timeOld⟩ →
    (∀ a < shape.volume, (p.member stateName).index a ≠ p.member "time") →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3Reset" (arguments (some p)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, finalHeap heap p shape⟩
  restores : ∀ heap p, Reads (finalHeap heap p shape) (p.member stateName) (zeroValues shape)
  null : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap),
    program.internal.definitions "fmi3Reset" = some (.tree (function shape)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3Reset" (arguments none) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

theorem contract (shape : Tensor.Shape) : Contract shape (function shape).render where
  printed := rfl
  closed := body_closed shape
  denotes := function_denotes shape
  successful program heap p kind mode timeOld bounded defined hk hm allowed writable timeCell separate :=
    reset_behaviors program shape heap p kind mode timeOld bounded defined hk hm allowed writable
      timeCell separate
  restores heap p := reads_initialization shape heap p
  null program heap defined := null_behaviors program shape heap defined

end

end Rumoca.FMI3.TensorReset
