import RumocaFMI3.TensorReset
import RumocaFMI3.Termination

/-! Tensor Model Exchange mode-transition bodies over the static tensor instance
record, as package-checked products.

The Model Exchange mode transitions `fmi3EnterInitializationMode`,
`fmi3ExitInitializationMode`, `fmi3EnterEventMode`, `fmi3EnterContinuousTimeMode`
and `fmi3Terminate` each validate the instance handle and lifecycle guard exactly
as the scalar bodies do (`Runtime.require` with the corresponding command), then
write the single lifecycle-mode field of the instance record and return `fmi3OK`.
Each body is `Runtime.require cmd ++ [Runtime.setMode after, Runtime.ok]`, so a
successful transition changes only the `mode` cell of the addressed instance and
preserves every other cell, including every cell of every other instance in the
static pool. A null handle is rejected with `fmi3Error`; a call issued in an
illegal mode reaches the shared `fail` statement and returns `fmi3Error` with
logging suppressed, after entering the Terminated mode as the scalar rejection
does (FMI 3.0.2 §2.3.1).

These bodies are shape-independent: they never read or write a tensor region, so
they are stated over an arbitrary instance address and specialized to the static
pool record only in the framing corollaries. This is a package-checked product
only: no production artifact is emitted, no CLI or grammar case is added, and the
scalar adapter, `Runtime.lean` and every existing contract are unchanged. -/
noncomputable section
namespace Rumoca.FMI3.TensorLifecycleModes
open CTree CMemory CBody
open Rumoca.FMI3.LifecycleBodies (writeMode)

/-- The Model Exchange mode transitions delivered here. -/
inductive Phase where
  | enterInitialization | exitInitialization | enterEvent | enterContinuous | terminate
  deriving DecidableEq

/-- The lifecycle command whose guard each transition applies. -/
def Phase.command : Phase → Command
  | .enterInitialization => .enterInitialization
  | .exitInitialization => .exitInitialization
  | .enterEvent => .enterEvent
  | .enterContinuous => .enterContinuous
  | .terminate => .terminate

/-- The lifecycle mode each transition writes. Exit-initialization enters Event
Mode for the Model Exchange profile (`nextMode .exitInitialization .me`). -/
def Phase.after : Phase → Mode
  | .enterInitialization => .initialization
  | .exitInitialization => .event
  | .enterEvent => .event
  | .enterContinuous => .continuous
  | .terminate => .terminated

/-- The public FMI 3 function name of each transition. -/
def Phase.name : Phase → String
  | .enterInitialization => "fmi3EnterInitializationMode"
  | .exitInitialization => "fmi3ExitInitializationMode"
  | .enterEvent => "fmi3EnterEventMode"
  | .enterContinuous => "fmi3EnterContinuousTimeMode"
  | .terminate => "fmi3Terminate"

def signature (ph : Phase) : Signature := ⟨"fmi3Status", ph.name, [⟨"fmi3Instance", "instance", false⟩]⟩

def arguments (handle : Option Address) : List Value := [.pointer handle]

def parameters (handle : Option Address) : Locals := bind (fun _ => none) "instance" (.pointer handle)

/-- The statements after the handle/lifecycle guard: write the single mode field
and return `fmi3OK`. -/
def tail (ph : Phase) : List Stmt := [Runtime.setMode ph.after, Runtime.ok]

def body (ph : Phase) : List Stmt := Runtime.require ph.command ++ tail ph

def function (ph : Phase) : CTree.Function := ⟨signature ph, body ph, false⟩

theorem body_closed (ph : Phase) :
    (function ph).body.all CBodyEmbedding.closedBlocks = true := by
  cases ph <;>
    simp [function, body, tail, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard,
      Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, Runtime.setMode, Runtime.put,
      Runtime.ok, Phase.command, Phase.after, CBodyEmbedding.closedBlocks, CLoops.noDeclarations]

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem parameters_bound (ph : Phase) (handle : Option Address) :
    CCalls.parameters (signature ph).parameters (arguments handle) = some (parameters handle) := by
  cases ph <;> rfl

/-- The whole transition body runs to the single mode write and success return.
Composed from the shared lifecycle guard and the two-statement tail, so the body
is established without unfolding any tensor region. -/
theorem body_run (ph : Phase) (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (allowed : Reference.Allowed ph.command kind mode) :
    CBody.run 5 (.running (body ph) (parameters (some p)) heap) =
      some (.returned ⟨.integer 0, writeMode heap p ph.after⟩) := by
  have hmode : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have entered := LifecycleGuard.accept (parameters (some p)) heap p ph.command kind mode
    (tail ph) (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hmode allowed
  rw [body, show (5 : Nat) = 3 + 2 from rfl, CBody.run_add, entered]
  cases ph <;>
    simp [tail, Phase.after, run, next, Runtime.setMode, Runtime.put, Runtime.field, Runtime.v,
      Runtime.mode, Runtime.n, Runtime.ok, Runtime.ret, Mode.code, eval, lvalue, parameters,
      CBody.bind, resolve, constants, Value.address, store, hm, convert, writeMode]

theorem call_behaviors (ph : Phase) (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
    (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions (signature ph).name = some (.tree (function ph)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (allowed : Reference.Allowed ph.command kind mode) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature ph).name (arguments (some p)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, writeMode heap p ph.after⟩ := by
  apply CCalls.Events.body_call_behaviors program (function ph) (arguments (some p))
    (parameters (some p)) heap ⟨.integer 0, writeMode heap p ph.after⟩ (.integer 0) 5 defined
    (parameters_bound ph _) (body_closed ph)
  · exact body_run ph heap p kind mode hk hm allowed
  · cases ph <;> simp [function, signature, Phase.name, CCalls.returnCast, CBody.cast, convert]

theorem null_behaviors (ph : Phase) (program : CCalls.Events.Program E) (heap : Heap)
    (defined : program.internal.definitions (signature ph).name = some (.tree (function ph)))
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature ph).name (arguments none) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (function ph)
    (Runtime.modeGuard ph.command :: tail ph)
    (arguments none) (parameters none) heap defined (parameters_bound ph _)
    (by cases ph <;> simp [function, body, tail, Runtime.require, List.append_assoc])
    rfl (body_closed ph)
  all_goals simp [parameters, CBody.bind]

/-- An illegal-mode call reaches the shared `fail` statement with the heap
unchanged. -/
theorem illegal_prefix (ph : Phase) (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (denied : ¬ Reference.Allowed ph.command kind mode) :
    GuardedCalls.FailurePrefix (function ph) (arguments (some p)) heap p
      ErrorCalls.rejectionMessage heap := by
  have reached := LifecycleGuard.reject_prefix (parameters (some p)) heap p ph.command kind mode
    (tail ph) (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hm denied
  refine ⟨rfl, body_closed ph, parameters (some p),
    CBody.bind (parameters (some p)) "m" (.pointer (some p)), tail ph, 3, parameters_bound ph _, ?_, ?_, ?_⟩
  · simpa only [function, body] using reached
  · simp [parameters, CBody.bind]
  · simp [CBody.bind, CBody.resolve]

/-- The illegal-mode rejection returns `fmi3Error` with logging suppressed, after
entering the Terminated mode. -/
theorem illegal_behaviors (ph : Phase) (program : CCalls.Events.Program E) (heap : Heap)
    (p message : Address) (kind : Kind) (mode : Mode) (logger : Option Address)
    (defined : program.internal.definitions (signature ph).name = some (.tree (function ph)))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (literal : static.addresses ErrorCalls.rejectionMessage = some message)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0))
    (denied : ¬ Reference.Allowed ph.command kind mode) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature ph).name (arguments (some p)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, writeMode heap p .terminated⟩ := by
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  exact GuardedCalls.FailurePrefix.silent_behaviors program (function ph) (arguments (some p)) heap heap
    p message ErrorCalls.rejectionMessage (some (.integer mode.code)) logger
    (illegal_prefix ph heap p kind mode hk modeLoaded denied) defined helper literal hm hl hg behavior

end

/-! ### Framing across instances of the static pool -/

/-- A successful transition of instance `i` changes only its `mode` cell, so it
preserves every tensor cell of every other instance of the static pool. -/
theorem preserves_other_instances (ph : Phase) (heap : Heap) (pool : Address) (i j : Nat)
    (b : String) (k : Nat) (different : j ≠ i) :
    writeMode heap (TensorInstance.record pool i) ph.after ((TensorInstance.field pool j b).index k) =
      heap ((TensorInstance.field pool j b).index k) := by
  apply LifecycleBodies.write_frame
  have sep := Address.instances_separate pool j i different b "mode" k 0
  simpa [TensorInstance.field, TensorInstance.record] using sep

/-! ### Printed text and denotation -/

section
open CTree.Printer CTree.Syntax

theorem signature_printable (ph : Phase) :
    SignaturePrintable RuntimePrinter.typedefs (signature ph) := by
  have statusType : TypeSpelling RuntimePrinter.typedefs "fmi3Status" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  have handleType : TypeSpelling RuntimePrinter.typedefs "fmi3Instance" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  cases ph <;>
    (refine ⟨statusType, by decide +kernel, ?_⟩
     intro param member
     simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
     rcases member with rfl
     exact ⟨handleType, by decide +kernel⟩)

theorem body_printable (ph : Phase) :
    ∀ stmt ∈ (function ph).body, ItemPrintable RuntimePrinter.typedefs stmt := by
  have iType : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
    .pointer (text := "Instance") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  cases ph <;>
    (simp only [function, body, tail, Phase.command, Phase.after, Runtime.require,
        Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression, permittedModes,
        Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, Runtime.setMode, Runtime.put,
        Runtime.ok, Runtime.field, Runtime.v, Runtime.n, Runtime.eqv, Runtime.both, Runtime.either,
        Runtime.negate, Runtime.any, Runtime.mode, Runtime.call, List.foldr_cons, List.foldr_nil,
        List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and,
        List.cons_append, List.nil_append, forall_eq] <;>
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

theorem function_denotes (ph : Phase) :
    FunctionDenotes RuntimePrinter.typedefs (function ph).render (function ph) :=
  CTree.Printer.function_denotes ⟨signature_printable ph, body_printable ph⟩

end

/-! ### The mode-transition contract -/

section
open CTree.Printer
variable [static : StaticLiterals]
private local instance contractInterface : CInterface := cInterface static.addresses

/-- The tensor mode-transition function contract, mirroring the scalar
`EventEntry.FunctionContract`/`Termination.FunctionContract` shapes. It bundles
the successful single-mode write, the null-handle rejection and the illegal-mode
rejection for one Model Exchange transition, so a tensor adapter contract can
consume them. -/
structure Contract (ph : Phase) (text : String) : Prop where
  printed : text = (function ph).render
  closed : (function ph).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text (function ph)
  successful : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
    (kind : Kind) (mode : Mode),
    program.internal.definitions (signature ph).name = some (.tree (function ph)) →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    Reference.Allowed ph.command kind mode →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature ph).name (arguments (some p)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, writeMode heap p ph.after⟩
  illegal : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (p message : Address)
    (kind : Kind) (mode : Mode) (logger : Option Address),
    program.internal.definitions (signature ph).name = some (.tree (function ph)) →
    program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
    static.addresses ErrorCalls.rejectionMessage = some message →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (.integer 0) →
    ¬ Reference.Allowed ph.command kind mode →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature ph).name (arguments (some p)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, writeMode heap p .terminated⟩
  null : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap),
    program.internal.definitions (signature ph).name = some (.tree (function ph)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature ph).name (arguments none) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

theorem contract (ph : Phase) : Contract ph (function ph).render where
  printed := rfl
  closed := body_closed ph
  denotes := function_denotes ph
  successful program heap p kind mode defined hk hm allowed :=
    call_behaviors ph program heap p kind mode defined hk hm allowed
  illegal program heap p message kind mode logger defined helper literal hk hm hl hg denied :=
    illegal_behaviors ph program heap p message kind mode logger defined helper literal hk hm hl hg denied
  null program heap defined := null_behaviors ph program heap defined

end

end Rumoca.FMI3.TensorLifecycleModes
