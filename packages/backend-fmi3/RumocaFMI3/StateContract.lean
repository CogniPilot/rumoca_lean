import RumocaFMI3.StateEntry
import RumocaFMI3.LoggingContract
import RumocaC.ObservedCalls

noncomputable section
namespace Rumoca.FMI3.StateCalls.Events
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory

theorem get_behaviors (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p buffer : Address) (mode : Mode) (state : ModelExchange.State) (old : Option Value)
    (defined : program.internal.definitions (signature false).name =
      some (.tree (Runtime.function model (signature false))))
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getStates .me mode)
    (represented : StateProofs.Represents heap p state)
    (storage : heap buffer = some ⟨.float64, true, old⟩) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature false).name (arguments p buffer) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0,
        StateProofs.written heap buffer (Binary64.toBits (ModelExchange.getContinuousState state)).val⟩ := by
  apply CCalls.Events.body_call_behaviors program (Runtime.function model (signature false))
    (arguments p buffer) (StateProofs.parameters p buffer) heap
    ⟨.integer 0, StateProofs.written heap buffer (Binary64.toBits (ModelExchange.getContinuousState state)).val⟩
    (.integer 0) 6
    defined (parameters_bound false p buffer) (BodyEmbedding.body_closed model (signature false))
  · exact StateProofs.get_run model (signature false) rfl heap p buffer mode state.x old hk hm allowed represented storage
  · rfl

theorem set_behaviors (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p buffer : Address) (state : ModelExchange.State) (x : Binary64.Value)
    (defined : program.internal.definitions (signature true).name =
      some (.tree (Runtime.function model (signature true))))
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer 3))
    (input : load heap buffer = some (.finite x))
    (storage : heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite state.x)⟩) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature true).name (arguments p buffer) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, StateProofs.written heap (StateProofs.stateAddress p)
        (Binary64.toBits (ModelExchange.setContinuousState state x).x).val⟩ := by
  apply CCalls.Events.body_call_behaviors program (Runtime.function model (signature true))
    (arguments p buffer) (StateProofs.parameters p buffer) heap
    ⟨.integer 0, StateProofs.written heap (StateProofs.stateAddress p)
      (Binary64.toBits (ModelExchange.setContinuousState state x).x).val⟩ (.integer 0) 7
    defined (parameters_bound true p buffer) (BodyEmbedding.body_closed model (signature true))
  · exact StateProofs.set_run model (signature true) rfl heap p buffer x _ hk hm input storage
  · rfl

end Rumoca.FMI3.StateCalls.Events

namespace Rumoca.FMI3.StateCalls
open CTree CMemory CLiteral CCalls.Events

def FailureExecutionContract [interface : CInterface] (write : Bool) (reason : Entry.FailureReason)
    (program : CCalls.Events.Program Invocation) (category message : Address) (heap : Heap) (signed : Bool) : Prop :=
  ∀ (p logger : Address) (environment buffer : Option Address) (count : UInt64)
    (kind : Kind) (mode : Mode) (name : String) (effect : ReturningEffect (Logging.signature name)),
    program.addresses logger = some name →
    program.externals name = some (External.observed (Logging.signature name) effect) →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    Entry.FailureCondition reason write kind mode heap buffer count →
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature write).name (Entry.values (some p) buffer count) heap .done) behavior ↔
      (∃ value after, effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after ∧
        behavior = .terminates [⟨name, Logging.arguments environment category message⟩] ⟨.integer 3, after⟩) ∨
      ((∀ value after, ¬ effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after) ∧ behavior = .wrong [])) ∧
    (∀ value after, effect.execute (Logging.arguments environment category message)
      (LifecycleBodies.writeMode heap p .terminated) value after →
      Stored signed after category "logStatus" ∧ Stored signed after message (Entry.failureMessage reason))

def SilentExecutionContract [interface : CInterface] (write : Bool) (reason : Entry.FailureReason)
    (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ p buffer count kind mode logger,
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (.integer 0) →
    Entry.FailureCondition reason write kind mode heap buffer count →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature write).name (Entry.values (some p) buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

section
variable [static : StaticLiterals]
private local instance failureInterface : CInterface := cInterface static.addresses

theorem failure_execution_correct (model : Solve.FMI3Model source) (write : Bool) (reason : Entry.FailureReason)
    (program : CCalls.Events.Program Invocation) (category message : Address) (heap : Heap) (signed : Bool)
    (defined : program.internal.definitions (signature write).name =
      some (.tree (Runtime.function model (signature write))))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (literal : static.addresses "logStatus" = some category)
    (messageBound : static.addresses (Entry.failureMessage reason) = some message)
    (categoryStored : Stored signed heap category "logStatus")
    (messageStored : Stored signed heap message (Entry.failureMessage reason)) :
    FailureExecutionContract write reason program category message heap signed := by
  intro p logger environment buffer count kind mode name effect address external hk hm hl hg he condition
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have certified := Entry.failure_prefix model write reason heap p buffer count kind mode hk modeLoaded condition
  have all := GuardedCalls.FailurePrefix.all_behaviors program (Runtime.function model (signature write))
    (Entry.values (some p) buffer count) heap heap p message category logger (Entry.failureMessage reason)
    name environment _ (External.observed (Logging.signature name) effect) certified defined helper messageBound
    address external rfl literal hm hl hg he
  constructor
  · intro behavior
    exact (all behavior).trans (observed_choices effect _ _ (fun _ after => ⟨.integer 3, after⟩) behavior)
  · intro value after executed
    have successful := (all (.terminates [⟨name, Logging.arguments environment category message⟩] ⟨.integer 3, after⟩)).mpr
      (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := CCalls.Events.termination_preserves successful
    exact ⟨categoryStored.preserved preserved, messageStored.preserved preserved⟩

theorem silent_execution_correct (model : Solve.FMI3Model source) (write : Bool) (reason : Entry.FailureReason)
    (program : CCalls.Events.Program E) (message : Address) (heap : Heap)
    (defined : program.internal.definitions (signature write).name =
      some (.tree (Runtime.function model (signature write))))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses (Entry.failureMessage reason) = some message) :
    SilentExecutionContract write reason program heap := by
  intro p buffer count kind mode logger hk hm hl hg condition behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have certified := Entry.failure_prefix model write reason heap p buffer count kind mode hk modeLoaded condition
  exact GuardedCalls.FailurePrefix.silent_behaviors program (Runtime.function model (signature write))
    (Entry.values (some p) buffer count) heap heap p message (Entry.failureMessage reason) _ logger
    certified defined helper messageBound hm hl hg behavior

end
end Rumoca.FMI3.StateCalls

namespace Rumoca.FMI3.StateCalls
open CTree CMemory CLiteral CCalls.Events

structure QuietExecutionContract [interface : CInterface] (program : CCalls.Events.Program E) (heap : Heap) : Prop where
  get : ∀ p buffer mode state old,
    load heap (p.member "kind") = some (.integer 0) →
    load heap (p.member "mode") = some (.integer mode.code) →
    Reference.Allowed .getStates .me mode → StateProofs.Represents heap p state →
    heap buffer = some ⟨.float64, true, old⟩ →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature false).name (arguments p buffer) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0,
        StateProofs.written heap buffer (Binary64.toBits (ModelExchange.getContinuousState state)).val⟩
  set : ∀ p buffer state x,
    load heap (p.member "kind") = some (.integer 0) →
    load heap (p.member "mode") = some (.integer 3) →
    load heap buffer = some (.finite x) →
    heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite state.x)⟩ →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature true).name (arguments p buffer) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, StateProofs.written heap (StateProofs.stateAddress p)
        (Binary64.toBits (ModelExchange.setContinuousState state x).x).val⟩
  null : ∀ write buffer count behavior, (CCalls.Events.machine program).Behaves
    (.calling (signature write).name (Entry.values none buffer count) heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 3, heap⟩

section
variable [static : StaticLiterals]
private local instance quietInterface : CInterface := cInterface static.addresses

theorem quiet_execution_correct (model : Solve.FMI3Model source)
    (program : CCalls.Events.Program E) (heap : Heap)
    (defined : ∀ write, program.internal.definitions (signature write).name =
      some (.tree (Runtime.function model (signature write)))) : QuietExecutionContract program heap := by
  constructor
  · intro p buffer mode state old hk hm allowed represented storage behavior
    exact Events.get_behaviors model program heap p buffer mode state old (defined false)
      hk hm allowed represented storage behavior
  · intro p buffer state x hk hm loaded storage behavior
    exact Events.set_behaviors model program heap p buffer state x (defined true) hk hm loaded storage behavior
  · intro write buffer count behavior
    exact Entry.null_behaviors model write program heap buffer count (defined write) behavior

end

/-- Both accessors share one actual table and pool. All messages are collected
from the setter, which contains the shared guard messages and its finite check. -/
def PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop :=
  ∀ (before : Heap) (firstBlock : Nat) (signed : Bool), ∃ (category : Address) (messages : Entry.FailureReason → Address),
    pool.addresses firstBlock "logStatus" = some category ∧
    Stored signed (pool.install before firstBlock signed) category "logStatus" ∧
    (∀ reason, pool.addresses firstBlock (Entry.failureMessage reason) = some (messages reason) ∧
      Stored signed (pool.install before firstBlock signed) (messages reason) (Entry.failureMessage reason)) ∧
    (∀ (E : Type) (program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) E),
      @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program =
        LiteralPreparation.program model sigs →
      @QuietExecutionContract E (cInterface (pool.addresses firstBlock)) program (pool.install before firstBlock signed) ∧
      ∀ write reason, @SilentExecutionContract E (cInterface (pool.addresses firstBlock)) write reason program
        (pool.install before firstBlock signed)) ∧
    (∀ program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) Invocation,
      @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) Invocation program =
        LiteralPreparation.program model sigs →
      ∀ write reason, @FailureExecutionContract (cInterface (pool.addresses firstBlock)) write reason program
        category (messages reason) (pool.install before firstBlock signed) signed)

theorem failure_message_collected (model : Solve.FMI3Model source) (reason : Entry.FailureReason) :
    Entry.failureMessage reason ∈ functionTexts (Runtime.function model (signature true)) := by
  cases reason <;> simp [Entry.failureMessage, ErrorCalls.rejectionMessage, Runtime.function, Runtime.body,
    signature, Runtime.require, Runtime.instancePrefix, Runtime.reject, Runtime.branch, Runtime.fail,
    Runtime.ret, Runtime.scalarAccessCheck, Runtime.finite, Runtime.negate, Runtime.call, Runtime.v, Runtime.n,
    functionTexts, statementTexts, expressionTexts]

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : ∀ write, signature write ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  intro before firstBlock signed
  obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
    (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" Logging.category_collected firstBlock
  have each : ∀ reason, ∃ message, pool.addresses firstBlock (Entry.failureMessage reason) = some message := by
    intro reason
    exact LiteralPreparation.message_bound model sigs made (signature true) (member true)
      (Entry.failureMessage reason) (failure_message_collected model reason) firstBlock
  choose messages bound using each
  have categoryStored := pool.storage_valid before firstBlock signed "logStatus" category categoryBound
  have messageStored := fun reason => pool.storage_valid before firstBlock signed _ (messages reason) (bound reason)
  refine ⟨category, messages, categoryBound, categoryStored, fun reason => ⟨bound reason, messageStored reason⟩, ?_, ?_⟩
  · intro E program same
    have defined (write) : (@CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program).definitions
        (signature write).name = some (.tree (Runtime.function model (signature write))) := by
      rw [same]
      exact LiteralPreparation.function_bound model sigs unique (signature write) (member write)
    have helper : (@CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program).definitions
        "fail" = some (.tree Runtime.helpers[0]) := by
      rw [same]
      exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])
    exact ⟨quiet_execution_correct (static := ⟨pool.addresses firstBlock⟩) model program _ defined,
      fun write reason => silent_execution_correct (static := ⟨pool.addresses firstBlock⟩) model write reason program
        _ _ (defined write) helper (bound reason)⟩
  · intro program same write reason
    apply failure_execution_correct (static := ⟨pool.addresses firstBlock⟩) model write reason program
      category (messages reason) _ signed _ _ categoryBound (bound reason) categoryStored (messageStored reason)
    · rw [same]
      exact LiteralPreparation.function_bound model sigs unique (signature write) (member write)
    · rw [same]
      exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])

structure FunctionsContract (model : Solve.FMI3Model source) (sigs : List Signature) (texts : Bool → String) : Prop where
  member : ∀ write, signature write ∈ sigs
  printed : ∀ write, texts write = (Runtime.function model (signature write)).render
  tokenization : ∀ write, Printer.FunctionTokenization RuntimePrinter.typedefs (texts write)
    (Runtime.function model (signature write))
  prepared : ∀ pool, LiteralPreparation.prepare model sigs = some pool → PreparedContract model sigs pool

theorem rendered_contract (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : ∀ write, signature write ∈ sigs) :
    FunctionsContract model sigs (fun write => (Runtime.function model (signature write)).render) := by
  refine ⟨member, fun _ => rfl, ?_, fun _ made => prepared_correct model sigs unique member made⟩
  intro write
  apply RuntimePrinter.function_tokenization
  cases write
  all_goals refine ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)),
    by decide +kernel, ?_⟩
  all_goals intro param member
  all_goals simp only [signature, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl | rfl
  all_goals refine ⟨?_, by decide +kernel⟩
  all_goals first
    | exact Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel))
    | exact Syntax.TypeSpelling.const
        (show Syntax.TypeSpelling RuntimePrinter.typedefs "fmi3Float64" from
          Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)))

end Rumoca.FMI3.StateCalls


namespace Rumoca.FMI3.StateCalls
open CMemory
variable [interface : CInterface]

/-- Readback exposes the same finite state as Solve's Model Exchange view,
with exact payload bits and a frame for every other memory cell. -/
theorem QuietExecutionContract.get_refines (contract : QuietExecutionContract program heap)
    (p buffer : Address) (mode : Mode) (state : ModelExchange.State) (old : Option Value)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getStates .me mode)
    (represented : StateProofs.Represents heap p state)
    (storage : heap buffer = some ⟨.float64, true, old⟩) :
    ∃ after,
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (signature false).name (arguments p buffer) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, after⟩) ∧
      load after buffer = some (.finite (ModelExchange.getContinuousState state)) ∧
      StateProofs.Represents after p state ∧
      (∀ address, address ≠ buffer → after address = heap address) := by
  refine ⟨StateProofs.written heap buffer (Binary64.toBits state.x).val,
    contract.get p buffer mode state old hk hm allowed represented storage, ?_, ?_, ?_⟩
  · simp [StateProofs.written, load, convert, Value.finite, ModelExchange.getContinuousState]
  · by_cases same : StateProofs.stateAddress p = buffer
    · simp [StateProofs.Represents, StateProofs.written, load, convert, same, Value.finite]
    · change load _ (StateProofs.stateAddress p) = _
      simpa only [load, StateProofs.written_frame heap buffer (StateProofs.stateAddress p) _ same]
        using represented
  · intro address other
    exact StateProofs.written_frame heap buffer address _ other

/-- The setter changes precisely the stored Model Exchange state. In particular
it does not advance a solver or assert a trajectory for the importer's choices. -/
theorem QuietExecutionContract.set_refines (contract : QuietExecutionContract program heap)
    (p buffer : Address) (state : ModelExchange.State) (x : Binary64.Value)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer 3))
    (input : load heap buffer = some (.finite x))
    (storage : heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite state.x)⟩) :
    ∃ after,
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (signature true).name (arguments p buffer) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, after⟩) ∧
      StateProofs.Represents after p (ModelExchange.setContinuousState state x) ∧
      (∀ address, address ≠ StateProofs.stateAddress p → after address = heap address) :=
  ⟨StateProofs.written heap (StateProofs.stateAddress p) (Binary64.toBits x).val,
    contract.set p buffer state x hk hm input storage,
    StateProofs.written_represents heap p state x,
    fun address other => StateProofs.written_frame heap (StateProofs.stateAddress p) address _ other⟩

end Rumoca.FMI3.StateCalls
