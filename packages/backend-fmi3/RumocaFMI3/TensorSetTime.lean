import RumocaFMI3.TensorCountQueries
import RumocaFMI3.TensorInstanceRhs

/-! Tensor Model Exchange `fmi3SetTime` body over the static tensor instance
record, as a package-checked product.

The body validates the instance handle and lifecycle guard exactly as the scalar
body does (`Runtime.require` with the `setTime` command, admitted only in Model
Exchange continuous-time mode), rejects a non-finite time value, and writes the
finite time value into the instance's independent time base. The time base is the
scalar (rank-0) member of the tensor instance record, so the write targets a
single `double` cell; no tensor coordinate is enumerated.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and the scalar adapter, `Runtime.lean` and every
existing contract are unchanged. Every theorem is universal in the instance
address (and, for the instance-bound corollary, in the tensor shape and the
instance index of the static pool) and the heap. -/
noncomputable section
namespace Rumoca.FMI3.TensorSetTime
open CTree CMemory CBody
open Rumoca.FMI3.TensorFloat64 (reject_false run_one)
open Rumoca.FMI3.TensorInstance
open Binary64 (toBits)

def message : String := "Time is outside the permitted interval"

/-- The setter ABI: `(instance, time)`. -/
def signature : Signature :=
  ⟨"fmi3Status", "fmi3SetTime",
    [⟨"fmi3Instance", "instance", false⟩, ⟨"fmi3Float64", "time", false⟩]⟩

def arguments (handle : Option Address) (bits : BitVec 64) : List Value :=
  [.pointer handle, .float64 bits]

def parameters (handle : Option Address) (bits : BitVec 64) : Locals :=
  bind (bind (fun _ => none) "time" (.float64 bits)) "instance" (.pointer handle)

/-- The finiteness rejection: a non-finite time is refused before any write. -/
def finiteReject : Stmt :=
  Runtime.reject (Runtime.negate (Runtime.finite (Runtime.v "time"))) message

def tail : List Stmt := [Runtime.put "time" (Runtime.v "time"), Runtime.ok]

def body : List Stmt := Runtime.require .setTime ++ (finiteReject :: tail)

def function : CTree.Function := ⟨signature, body, false⟩

/-- The successful result heap: exactly the instance time cell holds the value. -/
def written (heap : Heap) (address : Address) (bits : BitVec 64) : Heap :=
  replace heap address ⟨.float64, true, some (.float64 bits)⟩

/-- Local bindings after the handle/lifecycle guard: the instance pointer. -/
def guardEnv (p : Address) (bits : BitVec 64) : Locals :=
  bind (parameters (some p) bits) "m" (.pointer (some p))

theorem body_closed : function.body.all CBodyEmbedding.closedBlocks = true := by
  simp [function, body, tail, finiteReject, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard,
    Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, Runtime.ok, Runtime.put, Runtime.field,
    Runtime.v, Runtime.negate, Runtime.finite, Runtime.call, CBodyEmbedding.closedBlocks,
    CLoops.noDeclarations]

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem parameters_bound (handle : Option Address) (bits : BitVec 64) :
    CCalls.parameters signature.parameters (arguments handle bits) =
      some (parameters handle bits) := by
  simp [signature, arguments, CCalls.parameters, CCalls.parameterType, parameters, CBody.cast, convert,
    CBody.bind]

/-- A finite time value passes the finiteness rejection. -/
theorem finite_pass (heap : Heap) (p : Address) (time : Binary64.Value) :
    CBody.eval (guardEnv p (toBits time).val) heap
      (Runtime.negate (Runtime.finite (Runtime.v "time"))) = some (boolean false) := by
  have hfin : (Value.float64 (toBits time).val).isFinite = some true := Value.isFinite_finite time
  simp (config := { decide := true }) [Runtime.negate, Runtime.finite, Runtime.call, Runtime.v,
    CBody.eval, guardEnv, parameters, CBody.bind, CBody.resolve, hfin, Value.truth, boolean]

/-- The time write stores the value into the instance time cell. -/
theorem time_write (heap : Heap) (p : Address) (bits : BitVec 64) (old : Option Value)
    (storage : heap (p.member "time") = some ⟨.float64, true, old⟩) :
    CBody.next (.running (tail) (guardEnv p bits) heap) =
      some (.running [Runtime.ok] (guardEnv p bits) (written heap (p.member "time") bits)) := by
  have hstore : store heap (p.member "time") (.float64 bits) =
      some (written heap (p.member "time") bits) := by
    rw [written]
    exact store_of_convert heap (p.member "time") old (.float64 bits) (.float64 bits) .float64
      (by decide) storage (by simp [convert])
  have hres : resolve (guardEnv p bits) "m" = some (.pointer (some p)) := by
    simp [guardEnv, parameters, CBody.bind, CBody.resolve]
  have htime : resolve (guardEnv p bits) "time" = some (.float64 bits) := by
    simp [guardEnv, parameters, CBody.bind, CBody.resolve]
  simp [tail, Runtime.put, Runtime.field, Runtime.v, CBody.next, CBody.eval, CBody.lvalue,
    htime, hres, Value.address, hstore]

/-- The whole body runs to the successful time write for a finite value. -/
theorem body_run (heap : Heap) (p : Address) (time : Binary64.Value) (kind : Kind) (mode : Mode)
    (old : Option Value)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setTime kind mode)
    (storage : heap (p.member "time") = some ⟨.float64, true, old⟩) :
    CBody.run 6 (.running body (parameters (some p) (toBits time).val) heap) =
      some (.returned ⟨.integer 0, written heap (p.member "time") (toBits time).val⟩) := by
  have accepted : CBody.run 3 (.running body (parameters (some p) (toBits time).val) heap) =
      some (.running (finiteReject :: tail) (guardEnv p (toBits time).val) heap) := by
    rw [body]
    exact LifecycleGuard.accept (parameters (some p) (toBits time).val) heap p .setTime kind mode
      (finiteReject :: tail) (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind])
      hk hm allowed
  have s_reject : CBody.run 1 (.running (finiteReject :: tail) (guardEnv p (toBits time).val) heap) =
      some (.running tail (guardEnv p (toBits time).val) heap) :=
    run_one (reject_false (guardEnv p (toBits time).val) heap _ message tail (finite_pass heap p time))
  have s_ok : CBody.next (.running [Runtime.ok] (guardEnv p (toBits time).val)
      (written heap (p.member "time") (toBits time).val)) =
      some (.returned ⟨.integer 0, written heap (p.member "time") (toBits time).val⟩) := by
    simp [Runtime.ok, Runtime.ret, Runtime.v, CBody.next, CBody.eval, guardEnv, parameters,
      CBody.bind, CBody.resolve, constants]
  rw [show (6 : Nat) = 3 + 3 from rfl, CBody.run_add, accepted, Option.bind_some,
    show (3 : Nat) = 1 + (1 + 1) from rfl, CBody.run_add, s_reject, Option.bind_some,
    CBody.run_add, run_one (time_write heap p (toBits time).val old storage), Option.bind_some,
    run_one s_ok]

theorem call_behaviors (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
    (time : Binary64.Value) (kind : Kind) (mode : Mode) (old : Option Value)
    (defined : program.internal.definitions signature.name = some (.tree function))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setTime kind mode)
    (storage : heap (p.member "time") = some ⟨.float64, true, old⟩) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) (toBits time).val) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, written heap (p.member "time") (toBits time).val⟩ := by
  apply CCalls.Events.body_call_behaviors program function (arguments (some p) (toBits time).val)
    (parameters (some p) (toBits time).val) heap
    ⟨.integer 0, written heap (p.member "time") (toBits time).val⟩ (.integer 0) 6 defined
    (parameters_bound _ _) body_closed
  · exact body_run heap p time kind mode old hk hm allowed storage
  · simp [function, signature, CCalls.returnCast, CBody.cast, convert]

theorem null_behaviors (program : CCalls.Events.Program E) (heap : Heap) (bits : BitVec 64)
    (defined : program.internal.definitions signature.name = some (.tree function)) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments none bits) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program function (Runtime.modeGuard .setTime :: finiteReject :: tail)
    (arguments none bits) (parameters none bits) heap defined (parameters_bound _ _)
    (by simp [function, body, Runtime.require, List.append_assoc]) rfl body_closed
  all_goals simp [parameters, CBody.bind]

/-- A non-finite time is rejected: the body reaches the `fail` statement with the
heap unchanged. -/
theorem nonfinite_prefix (heap : Heap) (p : Address) (bits : BitVec 64) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setTime kind mode)
    (nonfinite : (Value.float64 bits).isFinite = some false) :
    GuardedCalls.FailurePrefix function (arguments (some p) bits) heap p message heap := by
  have accepted : CBody.run 3 (.running body (parameters (some p) bits) heap) =
      some (.running (finiteReject :: tail) (guardEnv p bits) heap) := by
    rw [body]
    exact LifecycleGuard.accept (parameters (some p) bits) heap p .setTime kind mode
      (finiteReject :: tail) (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind])
      hk hm allowed
  have hcond : CBody.eval (guardEnv p bits) heap
      (Runtime.negate (Runtime.finite (Runtime.v "time"))) = some (boolean true) := by
    simp (config := { decide := true }) [Runtime.negate, Runtime.finite, Runtime.call, Runtime.v,
      CBody.eval, guardEnv, parameters, CBody.bind, CBody.resolve, nonfinite, Value.truth, boolean]
  have s_reject : CBody.run 1 (.running (finiteReject :: tail) (guardEnv p bits) heap) =
      some (.running (Runtime.fail message :: tail) (guardEnv p bits) heap) :=
    run_one (Rumoca.FMI3.TensorFloat64.branch_true (guardEnv p bits) heap
      (Runtime.negate (Runtime.finite (Runtime.v "time"))) [Runtime.fail message] [] tail hcond)
  refine ⟨rfl, body_closed, parameters (some p) bits, guardEnv p bits, tail, 4,
    parameters_bound _ _, ?_, ?_, ?_⟩
  · show CBody.run 4 (.running body (parameters (some p) bits) heap) =
      some (.running (Runtime.fail message :: tail) (guardEnv p bits) heap)
    rw [show (4 : Nat) = 3 + 1 from rfl, CBody.run_add, accepted, Option.bind_some, s_reject]
  · simp [guardEnv, parameters, CBody.bind]
  · simp [guardEnv, parameters, CBody.bind, CBody.resolve]

/-- The non-finite rejection returns `fmi3Error` with logging suppressed. -/
theorem nonfinite_behaviors (program : CCalls.Events.Program E) (heap : Heap) (p message' : Address)
    (bits : BitVec 64) (kind : Kind) (mode : Mode) (logger : Option Address)
    (defined : program.internal.definitions signature.name = some (.tree function))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (literal : static.addresses message = some message')
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0))
    (allowed : Reference.Allowed .setTime kind mode)
    (nonfinite : (Value.float64 bits).isFinite = some false) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) bits) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  exact GuardedCalls.FailurePrefix.silent_behaviors program function (arguments (some p) bits) heap heap
    p message' message (some (.integer mode.code)) logger
    (nonfinite_prefix heap p bits kind mode hk modeLoaded allowed nonfinite)
    defined helper literal hm hl hg behavior

end

/-! ### Printed text and denotation -/

section
open CTree.Printer CTree.Syntax

theorem signature_printable : SignaturePrintable RuntimePrinter.typedefs signature := by
  refine ⟨.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel, ?_⟩
  intro param member
  simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩
  · exact ⟨.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩

theorem body_printable :
    ∀ stmt ∈ function.body, ItemPrintable RuntimePrinter.typedefs stmt := by
  have iType : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
    .pointer (text := "Instance") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  simp only [function, body, tail, finiteReject, Runtime.require, Runtime.instancePrefix,
      Runtime.modeGuard, Runtime.allowedExpression, permittedModes, Runtime.reject, Runtime.branch,
      Runtime.fail, Runtime.ret, Runtime.ok, Runtime.put, Runtime.field, Runtime.v, Runtime.n,
      Runtime.eqv, Runtime.both, Runtime.either, Runtime.negate, Runtime.any, Runtime.mode,
      Runtime.finite, Runtime.call, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, List.cons_append,
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
          Postfix, FieldBase]

theorem function_denotes :
    FunctionDenotes RuntimePrinter.typedefs function.render function :=
  CTree.Printer.function_denotes ⟨signature_printable, body_printable⟩

end

/-! ### Framing across instances -/

/-- The successful time write of instance `i` preserves every tensor cell of
every other instance of the static pool. -/
theorem preserves_other_instances (heap : Heap) (pool : Address) (i j : Nat) (bits : BitVec 64)
    (b : String) (k : Nat) (different : j ≠ i) :
    written heap (TensorInstance.field pool i timeName) bits
        ((TensorInstance.field pool j b).index k) = heap ((TensorInstance.field pool j b).index k) := by
  apply replace_other
  have sep := Address.instances_separate pool j i different b timeName k 0
  simpa [TensorInstance.field, TensorInstance.record] using sep

/-! ### The setter contract -/

section
open CTree.Printer
variable [static : StaticLiterals]
private local instance contractInterface : CInterface := cInterface static.addresses

/-- The tensor `fmi3SetTime` function contract. -/
structure Contract (text : String) : Prop where
  printed : text = function.render
  closed : function.body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text function
  successful : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
    (time : Binary64.Value) (kind : Kind) (mode : Mode) (old : Option Value),
    program.internal.definitions signature.name = some (.tree function) →
    load heap (p.member "kind") = some (.integer kind.code) →
    load heap (p.member "mode") = some (.integer mode.code) →
    Reference.Allowed .setTime kind mode →
    heap (p.member "time") = some ⟨.float64, true, old⟩ →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) (toBits time).val) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, written heap (p.member "time") (toBits time).val⟩
  null : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (bits : BitVec 64),
    program.internal.definitions signature.name = some (.tree function) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments none bits) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

theorem contract : Contract function.render where
  printed := rfl
  closed := body_closed
  denotes := function_denotes
  successful program heap p time kind mode old defined hk hm allowed storage :=
    call_behaviors program heap p time kind mode old defined hk hm allowed storage
  null program heap bits defined := null_behaviors program heap bits defined

end

end Rumoca.FMI3.TensorSetTime
