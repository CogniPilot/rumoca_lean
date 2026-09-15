import RumocaFMI3.Float64SetFailures
import RumocaFMI3.LoggingContract
import RumocaC.ObservedCalls
import RumocaFMI3.Float64SetWrite
import RumocaFMI3.Float64SetMetadata

noncomputable section
namespace Rumoca.FMI3.Float64Set
open CTree CMemory CLiteral CCalls.Events Float64Calls

def FailureExecutionContract [interface : CInterface] (reason : Failure)
    (program : CCalls.Events.Program Invocation) (category message : Address) (heap : Heap) (signed : Bool) : Prop :=
  ∀ (p logger : Address) (environment input buffer : Option Address) (n m : UInt64)
    (references : Nat → UInt32) (bits : Nat → BitVec 64) (kind : Kind) (mode : Mode)
    (name : String) (effect : ReturningEffect (Logging.signature name)),
    program.addresses logger = some name →
    program.externals name = some (External.observed (Logging.signature name) effect) →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    (reason = .entry → References heap input n.toNat references ∧
      ReadableValues heap buffer n.toNat references bits) →
    FailureCondition reason kind mode input buffer n m references bits →
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature true).name (arguments (some p) input buffer n m) heap .done) behavior ↔
      (∃ value after, effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after ∧
        behavior = .terminates [⟨name, Logging.arguments environment category message⟩] ⟨.integer 3, after⟩) ∨
      ((∀ value after, ¬ effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after) ∧ behavior = .wrong [])) ∧
    (∀ value after, effect.execute (Logging.arguments environment category message)
      (LifecycleBodies.writeMode heap p .terminated) value after →
      Stored signed after category "logStatus" ∧ Stored signed after message (failureMessage reason))

def SilentExecutionContract [interface : CInterface] (reason : Failure)
    (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ p input buffer n m references bits kind mode logger,
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (.integer 0) →
    (reason = .entry → References heap input n.toNat references ∧
      ReadableValues heap buffer n.toNat references bits) →
    FailureCondition reason kind mode input buffer n m references bits →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature true).name (arguments (some p) input buffer n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem failure_execution_correct (model : Solve.FMI3Model source) (reason : Failure)
    (program : CCalls.Events.Program Invocation) (category message : Address) (heap : Heap) (signed : Bool)
    (defined : program.internal.definitions (signature true).name =
      some (.tree (Runtime.function model (signature true))))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (literal : static.addresses "logStatus" = some category)
    (messageBound : static.addresses (failureMessage reason) = some message)
    (categoryStored : Stored signed heap category "logStatus")
    (messageStored : Stored signed heap message (failureMessage reason)) :
    FailureExecutionContract reason program category message heap signed := by
  intro p logger environment input buffer n m references bits kind mode name effect
    address external hk hm hl hg he readable condition
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have certified := failure_site model program heap p input buffer n m references bits kind mode reason
    defined hk modeLoaded readable condition
  have all := GuardedCalls.FailureSite.all_behaviors program _ heap p message category logger
    (failureMessage reason) name environment _ (External.observed (Logging.signature name) effect)
    certified helper messageBound address external rfl literal hm hl hg he
  constructor
  · intro behavior
    exact (all behavior).trans (observed_choices effect _ _ (fun _ after => ⟨.integer 3, after⟩) behavior)
  · intro value after executed
    have successful := (all (.terminates [⟨name, Logging.arguments environment category message⟩]
      ⟨.integer 3, after⟩)).mpr (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := CCalls.Events.termination_preserves successful
    exact ⟨categoryStored.preserved preserved, messageStored.preserved preserved⟩

theorem silent_execution_correct (model : Solve.FMI3Model source) (reason : Failure)
    (program : CCalls.Events.Program E) (message : Address) (heap : Heap)
    (defined : program.internal.definitions (signature true).name =
      some (.tree (Runtime.function model (signature true))))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses (failureMessage reason) = some message) :
    SilentExecutionContract reason program heap := by
  intro p input buffer n m references bits kind mode logger hk hm hl hg readable condition behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have certified := failure_site model program heap p input buffer n m references bits kind mode reason
    defined hk modeLoaded readable condition
  exact GuardedCalls.FailureSite.silent_behaviors program _ heap p message (failureMessage reason)
    _ logger certified helper messageBound hm hl hg behavior

end
end Rumoca.FMI3.Float64Set

noncomputable section
namespace Rumoca.FMI3.Float64Set
open CTree CMemory Float64Calls

structure QuietExecutionContract [interface : CInterface]
    (program : CCalls.Events.Program E) (heap : Heap) : Prop where
  set : ∀ (p input buffer : Address) (n : UInt64) (shape : Tensor.Shape)
    (values : TensorView.Values shape) (references : Nat → UInt32)
    (kind : Kind) (mode : Mode) (old : Option Value),
    shape.volume = n.toNat → 0 < shape.volume →
    load heap (p.member "kind") = some (.integer kind.code) →
    load heap (p.member "mode") = some (.integer mode.code) →
    Reference.Allowed .setStart kind mode →
    References heap (some input) shape.volume references →
    (∀ i < shape.volume, (references i).toNat = 1) →
    TensorView.Reads heap buffer values →
    heap (StateProofs.stateAddress p) = some ⟨.float64, true, old⟩ →
    (∀ i < shape.volume, StateProofs.stateAddress p ≠ buffer.index i) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature true).name (arguments (some p) (some input) (some buffer) n n) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, assigned heap p values shape.volume⟩
  empty : ∀ p input buffer (kind : Kind) (mode : Mode),
    load heap (p.member "kind") = some (.integer kind.code) →
    load heap (p.member "mode") = some (.integer mode.code) →
    Reference.Allowed .setVariables kind mode →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature true).name (arguments (some p) input buffer 0 0) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, heap⟩
  null : ∀ input buffer n m behavior, (CCalls.Events.machine program).Behaves
    (.calling (signature true).name (arguments none input buffer n m) heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 3, heap⟩

section
variable [static : StaticLiterals]
private local instance quietInterface : CInterface := cInterface static.addresses

theorem quiet_execution_correct (model : Solve.FMI3Model source)
    (program : CCalls.Events.Program E) (heap : Heap)
    (defined : program.internal.definitions (signature true).name =
      some (.tree (Runtime.function model (signature true)))) : QuietExecutionContract program heap := by
  constructor
  · intro p input buffer n shape values references kind mode old volume nonempty hk hm
      allowed readable valid loaded stored separate behavior
    exact set_behaviors model program heap p input buffer n values references kind mode old volume nonempty
      defined hk hm allowed readable valid loaded stored separate behavior
  · intro p input buffer kind mode hk hm permitted behavior
    exact empty_behaviors model program heap p input buffer kind mode defined hk hm permitted behavior
  · intro input buffer n m behavior
    exact null_behaviors model program heap input buffer n m defined behavior

end

section
variable [interface : CInterface]

/-- Every successful raw-bit request has an exact finite model interpretation.
The last request determines the state, with a frame for every other cell;
the caller supplies the original input storage, not a target execution trace. -/
theorem QuietExecutionContract.set_refines (contract : QuietExecutionContract program heap)
    (p input buffer : Address) (n : UInt64) (shape : Tensor.Shape)
    (references : Nat → UInt32) (bits : Nat → BitVec 64)
    (kind : Kind) (mode : Mode) (state : ModelExchange.State) (old : Option Value)
    (volume : shape.volume = n.toNat) (nonempty : 0 < shape.volume)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStart kind mode)
    (readable : References heap (some input) shape.volume references)
    (valid : ∀ i < shape.volume, ValidEntry (references i) (bits i))
    (loaded : ReadableValues heap (some buffer) shape.volume references bits)
    (stored : heap (StateProofs.stateAddress p) = some ⟨.float64, true, old⟩)
    (separate : ∀ i < shape.volume, StateProofs.stateAddress p ≠ buffer.index i) :
    ∃ after x,
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (signature true).name (arguments (some p) (some input) (some buffer) n n) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, after⟩) ∧
      (Binary64.toBits x).val = bits (shape.volume - 1) ∧
      StateProofs.Represents after p (ModelExchange.setContinuousState state x) ∧
      (∀ address, address ≠ StateProofs.stateAddress p → after address = heap address) := by
  obtain ⟨values, valuesRead, same⟩ := accepted_snapshot heap buffer shape references bits valid loaded
  refine ⟨assigned heap p values shape.volume, values[shape.volume - 1],
    contract.set p input buffer n shape values references kind mode old volume nonempty hk hm allowed
      readable (fun i inside => (valid i inside).1) valuesRead stored separate, ?_,
    assigned_represents heap p values state nonempty, ?_⟩
  · have last := same (shape.volume - 1) (by omega)
    rwa [bitsAt_inside values (shape.volume - 1) (by omega)] at last
  · intro address outside
    exact assigned_frame heap p values shape.volume address outside

end
end Rumoca.FMI3.Float64Set

noncomputable section
namespace Rumoca.FMI3.Float64Set
open CTree CMemory CLiteral CCalls.Events Float64Calls

/-- One actual function table and one installed literal pool supply successful,
empty, null and failed calls, including every specified logger outcome. -/
def PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop :=
  ∀ (before : Heap) (firstBlock : Nat) (signed : Bool), ∃ (category : Address) (messages : Failure → Address),
    pool.addresses firstBlock "logStatus" = some category ∧
    Stored signed (pool.install before firstBlock signed) category "logStatus" ∧
    (∀ reason, pool.addresses firstBlock (failureMessage reason) = some (messages reason) ∧
      Stored signed (pool.install before firstBlock signed) (messages reason) (failureMessage reason)) ∧
    (∀ (E : Type) (program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) E),
      @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program =
        LiteralPreparation.program model sigs →
      @QuietExecutionContract E (cInterface (pool.addresses firstBlock)) program
        (pool.install before firstBlock signed) ∧
      ∀ reason, @SilentExecutionContract E (cInterface (pool.addresses firstBlock)) reason program
        (pool.install before firstBlock signed)) ∧
    (∀ program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) Invocation,
      @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) Invocation program =
        LiteralPreparation.program model sigs →
      ∀ reason, @FailureExecutionContract (cInterface (pool.addresses firstBlock)) reason program
        category (messages reason) (pool.install before firstBlock signed) signed)

theorem failure_message_collected (model : Solve.FMI3Model source) (reason : Failure) :
    failureMessage reason ∈ functionTexts (Runtime.function model (signature true)) := by
  cases reason <;> simp [failureMessage, message, ErrorCalls.rejectionMessage,
    Runtime.function, Runtime.body, signature, Runtime.setFloat64, Runtime.setFloat64Values,
    Runtime.instancePrefix, Runtime.reject, Runtime.branch, Runtime.fail,
    Runtime.ret, Runtime.countLoop, Runtime.negate, Runtime.call, Runtime.v, Runtime.n,
    functionTexts, statementTexts, expressionTexts]

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature true ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  intro before firstBlock signed
  obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
    (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" Logging.category_collected firstBlock
  have each : ∀ reason, ∃ message, pool.addresses firstBlock (failureMessage reason) = some message := by
    intro reason
    exact LiteralPreparation.message_bound model sigs made (signature true) member
      (failureMessage reason) (failure_message_collected model reason) firstBlock
  choose messages bound using each
  have categoryStored := pool.storage_valid before firstBlock signed "logStatus" category categoryBound
  have messageStored := fun reason => pool.storage_valid before firstBlock signed _ (messages reason) (bound reason)
  refine ⟨category, messages, categoryBound, categoryStored,
    fun reason => ⟨bound reason, messageStored reason⟩, ?_, ?_⟩
  · intro E program same
    have defined : (@CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program).definitions
        (signature true).name = some (.tree (Runtime.function model (signature true))) := by
      rw [same]
      exact LiteralPreparation.function_bound model sigs unique (signature true) member
    have helper : (@CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program).definitions
        "fail" = some (.tree Runtime.helpers[0]) := by
      rw [same]
      exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])
    exact ⟨quiet_execution_correct (static := ⟨pool.addresses firstBlock⟩) model program _ defined,
      fun reason => silent_execution_correct (static := ⟨pool.addresses firstBlock⟩) model reason program
        _ _ defined helper (bound reason)⟩
  · intro program same reason
    apply failure_execution_correct (static := ⟨pool.addresses firstBlock⟩) model reason program
      category (messages reason) _ signed _ _ categoryBound (bound reason) categoryStored (messageStored reason)
    · rw [same]
      exact LiteralPreparation.function_bound model sigs unique (signature true) member
    · rw [same]
      exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])

structure FunctionContract (model : Solve.FMI3Model source) (sigs : List Signature) (text : String) : Prop where
  member : signature true ∈ sigs
  printed : text = (Runtime.function model (signature true)).render
  tokenization : Printer.FunctionTokenization RuntimePrinter.typedefs text (Runtime.function model (signature true))
  prepared : ∀ pool, LiteralPreparation.prepare model sigs = some pool → PreparedContract model sigs pool

theorem rendered_contract (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature true ∈ sigs) :
    FunctionContract model sigs (Runtime.function model (signature true)).render := by
  refine ⟨member, rfl, ?_, fun _ made => prepared_correct model sigs unique member made⟩
  apply RuntimePrinter.function_tokenization
  refine ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)),
    by decide +kernel, ?_⟩
  intro param member
  simp only [signature, List.mem_cons, List.not_mem_nil, or_false, ↓reduceIte] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_, by decide +kernel⟩
  all_goals first
    | exact Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel))
    | exact Syntax.TypeSpelling.const
        (show Syntax.TypeSpelling RuntimePrinter.typedefs "fmi3ValueReference" from
          Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)))
    | exact Syntax.TypeSpelling.const
        (show Syntax.TypeSpelling RuntimePrinter.typedefs "fmi3Float64" from
          Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)))

theorem metadata_selection (source : AST.Model) (root : XML.Element)
    (metadata : Float64SetMetadata.Writable root 1 source.state)
    (reference : UInt32) (bits : BitVec 64) (valid : ValidEntry reference bits) :
    Float64SetMetadata.Writable root reference.toNat source.state := by
  rw [valid.1]
  exact metadata

end Rumoca.FMI3.Float64Set
