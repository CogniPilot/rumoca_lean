import RumocaFMI3.TensorFloat64Access

/-! Tensor Model Exchange count-query bodies, as package-checked products.

`fmi3GetNumberOfContinuousStates` writes the symbolic state volume
(`shape.volume`) as a `size_t` into the caller's pointer;
`fmi3GetNumberOfEventIndicators` writes `0`. Each body validates the instance
handle and lifecycle guard exactly as the scalar bodies do (`Runtime.require`
with the `getCounts` command), checks that the output pointer is non-null, and
writes the single count with the scalar `pointerCheck`/`out`/`ok` shape. The
count is a compile-time constant for a given shape, so no tensor coordinate is
enumerated.

The successful write converts the count to the authored `size_t` profile. The
conversion is discharged through the reusable `CLoops.convert_size_nat` lemma
under an explicit `shape.volume < 2 ^ 64` premise, and the body run is composed
from the small machine steps rather than one large reduction, so the `2 ^ 64`
bound is never unfolded against the symbolic volume.

This is a package-checked product only: no production artifact is emitted, no
CLI or grammar case is added, and the scalar adapter, `Runtime.lean` and every
existing contract are unchanged. Every theorem is universal in the tensor shape,
the instance address, the request lengths and the heap. -/
noncomputable section

namespace Rumoca.CMemory
/-- A store whose conversion is supplied as an equation. The cell type stays
abstract, so the reduction of `store` never evaluates the conversion (hence
never the `2 ^ 64` `size_t` bound); the value is placed through `hconv` alone. -/
theorem store_of_convert (heap : Heap) (buffer : Address) (old : Option Value)
    (value result : Value) (t : CType) (hne : t ≠ .atomicBoolean)
    (hp : heap buffer = some ⟨t, true, old⟩)
    (hconv : convert t value = some result) :
    store heap buffer value = some (replace heap buffer ⟨t, true, some result⟩) := by
  have hguard : (t == CType.atomicBoolean) = false := by
    rw [Bool.eq_false_iff]; intro h; exact hne (eq_of_beq h)
  unfold store
  rw [hp]
  simp only [bind, Option.bind, hguard, Bool.not_true, Bool.or_false, Bool.false_eq_true,
    if_false, hconv]
  rfl
end Rumoca.CMemory

namespace Rumoca.FMI3.TensorCountQueries
open CTree CMemory CBody
open Rumoca.FMI3.TensorFloat64 (reject_false run_one)
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096

/-- The output parameter name for each count query. -/
def outputName (events : Bool) : String :=
  if events then "nEventIndicators" else "nContinuousStates"

/-- The written count: the symbolic state volume for continuous states, `0` for
event indicators. -/
def count (shape : Tensor.Shape) (events : Bool) : Nat :=
  if events then 0 else shape.volume

/-- The count query ABI: `(instance, count *)`. -/
def signature (events : Bool) : Signature :=
  ⟨"fmi3Status", if events then "fmi3GetNumberOfEventIndicators" else "fmi3GetNumberOfContinuousStates",
    [⟨"fmi3Instance", "instance", false⟩, ⟨"size_t *", outputName events, false⟩]⟩

def arguments (handle buffer : Option Address) : List Value := [.pointer handle, .pointer buffer]

def parameters (events : Bool) (handle buffer : Option Address) : Locals :=
  bind (bind (fun _ => none) (outputName events) (.pointer buffer)) "instance" (.pointer handle)

/-- The statements after the handle/lifecycle guard: pointer check, the single
count write, and the success return. -/
def rest (shape : Tensor.Shape) (events : Bool) : List Stmt :=
  [Runtime.pointerCheck [outputName events],
    Runtime.out (outputName events) (Runtime.n (count shape events)), Runtime.ok]

def body (shape : Tensor.Shape) (events : Bool) : List Stmt :=
  Runtime.require .getCounts ++ rest shape events

def function (shape : Tensor.Shape) (events : Bool) : CTree.Function :=
  ⟨signature events, body shape events, false⟩

/-- The result heap of a successful count query: exactly the output cell holds
the count. -/
def written (shape : Tensor.Shape) (events : Bool) (heap : Heap) (buffer : Address) : Heap :=
  replace heap buffer ⟨.size, true, some (.integer (count shape events))⟩

theorem count_bounded (shape : Tensor.Shape) (events : Bool) (bounded : shape.volume < 2 ^ 64) :
    count shape events < 2 ^ 64 := by
  cases events with
  | false => exact bounded
  | true => show 0 < 2 ^ 64; positivity

/-- Local bindings after the handle/lifecycle guard: the instance pointer. -/
def guardEnv (events : Bool) (p buffer : Address) : Locals :=
  bind (parameters events (some p) (some buffer)) "m" (.pointer (some p))

theorem body_closed (shape : Tensor.Shape) (events : Bool) :
    (function shape events).body.all CBodyEmbedding.closedBlocks = true := by
  cases events <;>
    simp [function, body, rest, outputName, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard,
      Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, Runtime.ok, Runtime.pointerCheck,
      Runtime.out, Runtime.v, Runtime.n, Runtime.any, CBodyEmbedding.closedBlocks, CLoops.noDeclarations]

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem parameters_bound (events : Bool) (handle buffer : Option Address) :
    CCalls.parameters (signature events).parameters (arguments handle buffer) =
      some (parameters events handle buffer) := by
  cases events <;> rfl

/-- The store of the size-typed count into the caller's output cell. The `size_t`
conversion is discharged by `convert_size_nat` under the volume bound; `2 ^ 64`
is never unfolded against the symbolic count. -/
theorem store_count (shape : Tensor.Shape) (events : Bool) (heap : Heap) (buffer : Address)
    (old : Option Value) (bounded : shape.volume < 2 ^ 64)
    (storage : heap buffer = some ⟨.size, true, old⟩) :
    store heap buffer (.integer (count shape events)) = some (written shape events heap buffer) := by
  have hconv : convert .size (.integer (count shape events)) = some (.integer (count shape events)) :=
    CLoops.convert_size_nat _ (count_bounded shape events bounded)
  rw [written, store_of_convert heap buffer old (.integer (count shape events))
    (.integer (count shape events)) .size (by decide) storage hconv]

/-- The pointer check passes for a non-null output pointer. -/
theorem pointer_pass (events : Bool) (heap : Heap) (p buffer : Address) :
    CBody.eval (guardEnv events p buffer) heap
      (Runtime.any [Runtime.negate (Runtime.v (outputName events))]) = some (boolean false) := by
  cases events <;>
    simp [Runtime.any, Runtime.either, Runtime.negate, Runtime.v, Runtime.n, CBody.eval, guardEnv,
      parameters, outputName, CBody.bind, CBody.resolve, Value.truth, boolean]

/-- The whole count-query body runs to the successful count write. Composed from
the guard, pointer check, single write and return, so the `size_t` conversion is
the only place the volume bound is used. -/
theorem body_run (shape : Tensor.Shape) (events : Bool) (heap : Heap) (p buffer : Address)
    (kind : Kind) (mode : Mode) (old : Option Value)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getCounts kind mode) (bounded : shape.volume < 2 ^ 64)
    (storage : heap buffer = some ⟨.size, true, old⟩) :
    CBody.run 6 (.running (body shape events) (parameters events (some p) (some buffer)) heap) =
      some (.returned ⟨.integer 0, written shape events heap buffer⟩) := by
  have accepted : CBody.run 3 (.running (body shape events)
      (parameters events (some p) (some buffer)) heap) =
      some (.running (rest shape events) (guardEnv events p buffer) heap) := by
    rw [body]
    exact LifecycleGuard.accept (parameters events (some p) (some buffer)) heap p
      .getCounts kind mode (rest shape events)
      (by cases events <;> simp [parameters, CBody.bind])
      (by cases events <;> simp [parameters, outputName, CBody.bind]) hk hm allowed
  -- pointer check falls through
  have s_check : CBody.run 1 (.running (rest shape events) (guardEnv events p buffer) heap) =
      some (.running (Runtime.out (outputName events) (Runtime.n (count shape events)) :: [Runtime.ok])
        (guardEnv events p buffer) heap) :=
    run_one (by
      simpa only [rest, Runtime.pointerCheck, List.map_cons, List.map_nil] using
        reject_false (guardEnv events p buffer) heap
          (Runtime.any [Runtime.negate (Runtime.v (outputName events))]) "Missing output pointer"
          [Runtime.out (outputName events) (Runtime.n (count shape events)), Runtime.ok]
          (pointer_pass events heap p buffer))
  -- the single count write
  have hbufResolve : resolve (guardEnv events p buffer) (outputName events) = some (.pointer (some buffer)) := by
    cases events <;> simp [guardEnv, parameters, outputName, CBody.bind, CBody.resolve]
  have s_write : CBody.next (.running
      (Runtime.out (outputName events) (Runtime.n (count shape events)) :: [Runtime.ok])
      (guardEnv events p buffer) heap) =
      some (.running [Runtime.ok] (guardEnv events p buffer) (written shape events heap buffer)) := by
    simp [Runtime.out, Runtime.n, Runtime.v, CBody.next, CBody.eval, CBody.lvalue,
      hbufResolve, Value.address, store_count shape events heap buffer old bounded storage]
  -- the success return
  have s_ok : CBody.next (.running [Runtime.ok] (guardEnv events p buffer)
      (written shape events heap buffer)) =
      some (.returned ⟨.integer 0, written shape events heap buffer⟩) := by
    cases events <;>
      simp [Runtime.ok, Runtime.ret, Runtime.v, CBody.next, CBody.eval, guardEnv, parameters, outputName,
        CBody.bind, CBody.resolve, constants]
  rw [show (6 : Nat) = 3 + 3 from rfl, CBody.run_add, accepted, Option.bind_some,
    show (3 : Nat) = 1 + (1 + 1) from rfl, CBody.run_add, s_check, Option.bind_some,
    CBody.run_add, run_one s_write, Option.bind_some, run_one s_ok]

theorem call_behaviors (shape : Tensor.Shape) (events : Bool) (program : CCalls.Events.Program E)
    (heap : Heap) (p buffer : Address) (kind : Kind) (mode : Mode) (old : Option Value)
    (defined : program.internal.definitions (signature events).name = some (.tree (function shape events)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getCounts kind mode) (bounded : shape.volume < 2 ^ 64)
    (storage : heap buffer = some ⟨.size, true, old⟩) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature events).name (arguments (some p) (some buffer)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, written shape events heap buffer⟩ := by
  apply CCalls.Events.body_call_behaviors program (function shape events) (arguments (some p) (some buffer))
    (parameters events (some p) (some buffer)) heap ⟨.integer 0, written shape events heap buffer⟩
    (.integer 0) 6 defined (parameters_bound events _ _) (body_closed shape events)
  · exact body_run shape events heap p buffer kind mode old hk hm allowed bounded storage
  · cases events <;> simp [function, signature, CCalls.returnCast, CBody.cast, convert]

theorem null_behaviors (shape : Tensor.Shape) (events : Bool) (program : CCalls.Events.Program E)
    (heap : Heap) (buffer : Option Address)
    (defined : program.internal.definitions (signature events).name = some (.tree (function shape events)))
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature events).name (arguments none buffer) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (function shape events)
    (Runtime.modeGuard .getCounts :: rest shape events)
    (arguments none buffer) (parameters events none buffer) heap defined
    (parameters_bound events _ _)
    (by cases events <;> simp [function, body, rest, outputName, Runtime.require, List.append_assoc])
    rfl (body_closed shape events)
  all_goals cases events <;> simp [parameters, outputName, CBody.bind]

end

/-! ### Printed text and denotation -/

section
open CTree.Printer CTree.Syntax

theorem signature_printable (events : Bool) :
    SignaturePrintable RuntimePrinter.typedefs (signature events) := by
  have statusType : TypeSpelling RuntimePrinter.typedefs "fmi3Status" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  have handleType : TypeSpelling RuntimePrinter.typedefs "fmi3Instance" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  have sizeType : TypeSpelling RuntimePrinter.typedefs "size_t" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  cases events <;>
    (refine ⟨statusType, by decide +kernel, ?_⟩
     intro param member
     simp only [signature, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil,
        or_false] at member
     rcases member with rfl | rfl
     · exact ⟨handleType, by decide +kernel⟩
     · exact ⟨TypeSpelling.pointer sizeType, by decide +kernel⟩)

theorem body_printable (shape : Tensor.Shape) (events : Bool) :
    ∀ stmt ∈ (function shape events).body, ItemPrintable RuntimePrinter.typedefs stmt := by
  have iType : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
    .pointer (text := "Instance") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  cases events <;>
    (simp only [function, body, rest, outputName, Bool.false_eq_true, ↓reduceIte, Runtime.require,
        Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression, permittedModes,
        Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, Runtime.ok, Runtime.pointerCheck,
        Runtime.out, Runtime.field, Runtime.v, Runtime.n, Runtime.eqv, Runtime.both, Runtime.either,
        Runtime.negate, Runtime.any, Runtime.mode, Runtime.call, List.foldr_cons, List.foldr_nil, List.map_cons,
        List.map_nil, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, List.cons_append,
        List.nil_append, forall_eq] <;>
      repeat first
        | exact CNull.literal_printable _
        | exact iType
        | apply And.intro
        | apply ItemPrintable.declare
        | apply ItemPrintable.assign
        | apply ItemPrintable.branch
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
            Postfix, FieldBase])

theorem function_denotes (shape : Tensor.Shape) (events : Bool) :
    FunctionDenotes RuntimePrinter.typedefs (function shape events).render (function shape events) :=
  CTree.Printer.function_denotes ⟨signature_printable events, body_printable shape events⟩

end

/-! ### The count-query contract -/

section
open CTree.Printer
variable [static : StaticLiterals]
private local instance contractInterface : CInterface := cInterface static.addresses

/-- The tensor count-query function contract, universal in the tensor shape. -/
structure Contract (shape : Tensor.Shape) (events : Bool) (text : String) : Prop where
  printed : text = (function shape events).render
  closed : (function shape events).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text (function shape events)
  successful : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (p buffer : Address)
    (kind : Kind) (mode : Mode) (old : Option Value),
    program.internal.definitions (signature events).name = some (.tree (function shape events)) →
    load heap (p.member "kind") = some (.integer kind.code) →
    load heap (p.member "mode") = some (.integer mode.code) →
    Reference.Allowed .getCounts kind mode → shape.volume < 2 ^ 64 →
    heap buffer = some ⟨.size, true, old⟩ →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature events).name (arguments (some p) (some buffer)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, written shape events heap buffer⟩
  null : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (buffer : Option Address),
    program.internal.definitions (signature events).name = some (.tree (function shape events)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature events).name (arguments none buffer) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

theorem contract (shape : Tensor.Shape) (events : Bool) :
    Contract shape events (function shape events).render where
  printed := rfl
  closed := body_closed shape events
  denotes := function_denotes shape events
  successful program heap p buffer kind mode old defined hk hm allowed bounded storage :=
    call_behaviors shape events program heap p buffer kind mode old defined hk hm allowed bounded storage
  null program heap buffer defined :=
    null_behaviors shape events program heap buffer defined

end

end Rumoca.FMI3.TensorCountQueries
