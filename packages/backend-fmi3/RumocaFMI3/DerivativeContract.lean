import RumocaFMI3.DerivativeFailures
import RumocaFMI3.ModelRhs
import RumocaFMI3.LoggingContract
import RumocaC.ObservedCalls

noncomputable section
namespace Rumoca.FMI3.DerivativeCalls
open CTree CMemory CLiteral CCalls.Events

def FailureExecutionContract [interface : CInterface] (access : Bool)
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
    FailureCondition access kind mode buffer count →
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (values (some p) buffer count) heap .done) behavior ↔
      (∃ value after, effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after ∧
        behavior = .terminates [⟨name, Logging.arguments environment category message⟩] ⟨.integer 3, after⟩) ∨
      ((∀ value after, ¬ effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after) ∧ behavior = .wrong [])) ∧
    (∀ value after, effect.execute (Logging.arguments environment category message)
      (LifecycleBodies.writeMode heap p .terminated) value after →
      Stored signed after category "logStatus" ∧ Stored signed after message (failureMessage access))

def SilentExecutionContract [interface : CInterface] (access : Bool)
    (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ p buffer count kind mode logger,
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (.integer 0) →
    FailureCondition access kind mode buffer count →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (values (some p) buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

structure QuietExecutionContract [interface : CInterface] (model : Solve.FMI3Model source)
    (program : CCalls.Events.Program E) (heap : Heap) : Prop where
  get : ∀ p buffer mode state old,
    load heap (p.member "kind") = some (.integer 0) →
    load heap (p.member "mode") = some (.integer mode.code) →
    Reference.Allowed .getDerivatives .me mode →
    heap buffer = some ⟨.float64, true, old⟩ →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (values (some p) (some buffer) 1) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, StateProofs.written heap buffer
        (Binary64.toBits (ModelExchange.derivative model.solve state)).val⟩
  null : ∀ buffer count behavior, (CCalls.Events.machine program).Behaves
    (.calling signature.name (values none buffer count) heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 3, heap⟩

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem failure_execution_correct (model : Solve.FMI3Model source) (access : Bool)
    (program : CCalls.Events.Program Invocation) (category message : Address) (heap : Heap) (signed : Bool)
    (defined : program.internal.definitions signature.name = some (.tree (Runtime.function model signature)))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (literal : static.addresses "logStatus" = some category)
    (messageBound : static.addresses (failureMessage access) = some message)
    (categoryStored : Stored signed heap category "logStatus")
    (messageStored : Stored signed heap message (failureMessage access)) :
    FailureExecutionContract access program category message heap signed := by
  intro p logger environment buffer count kind mode name effect address external hk hm hl hg he condition
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have certified := failure_prefix model access heap p buffer count kind mode hk modeLoaded condition
  have all := GuardedCalls.FailurePrefix.all_behaviors program (Runtime.function model signature)
    (values (some p) buffer count) heap heap p message category logger (failureMessage access)
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

theorem silent_execution_correct (model : Solve.FMI3Model source) (access : Bool)
    (program : CCalls.Events.Program E) (message : Address) (heap : Heap)
    (defined : program.internal.definitions signature.name = some (.tree (Runtime.function model signature)))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses (failureMessage access) = some message) :
    SilentExecutionContract access program heap := by
  intro p buffer count kind mode logger hk hm hl hg condition behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have certified := failure_prefix model access heap p buffer count kind mode hk modeLoaded condition
  exact GuardedCalls.FailurePrefix.silent_behaviors program (Runtime.function model signature)
    (values (some p) buffer count) heap heap p message (failureMessage access) _ logger
    certified defined helper messageBound hm hl hg behavior

theorem quiet_execution_correct (model : Solve.FMI3Model source)
    (program : CCalls.Events.Program E) (heap : Heap)
    (defined : program.internal.definitions signature.name = some (.tree (Runtime.function model signature)))
    (helper : program.internal.definitions "model_rhs" = some (.tree Runtime.helpers[1]))
    (numerical : program.internal.definitions "rumoca_rhs" = some (.kernel .rhs))
    (same : program.internal.kernel = CExecution.program model.solve) : QuietExecutionContract model program heap := by
  constructor
  · intro p buffer mode state old hk hm allowed storage behavior
    exact behaviors model program heap p buffer mode state old defined helper numerical same hk hm allowed storage behavior
  · intro buffer count behavior
    exact null_behaviors model program heap buffer count defined behavior

end

def PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop :=
  ∀ (before : Heap) (firstBlock : Nat) (signed : Bool), ∃ (category : Address) (messages : Bool → Address),
    pool.addresses firstBlock "logStatus" = some category ∧
    Stored signed (pool.install before firstBlock signed) category "logStatus" ∧
    (∀ access, pool.addresses firstBlock (failureMessage access) = some (messages access) ∧
      Stored signed (pool.install before firstBlock signed) (messages access) (failureMessage access)) ∧
    (∀ (E : Type) (program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) E),
      @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program =
        LiteralPreparation.program model sigs →
      @QuietExecutionContract source E (cInterface (pool.addresses firstBlock)) model program
        (pool.install before firstBlock signed) ∧
      ∀ access, @SilentExecutionContract E (cInterface (pool.addresses firstBlock)) access program
        (pool.install before firstBlock signed)) ∧
    (∀ program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) Invocation,
      @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) Invocation program =
        LiteralPreparation.program model sigs →
      ∀ access, @FailureExecutionContract (cInterface (pool.addresses firstBlock)) access program
        category (messages access) (pool.install before firstBlock signed) signed)

theorem failure_message_collected (model : Solve.FMI3Model source) (access : Bool) :
    failureMessage access ∈ functionTexts (Runtime.function model signature) := by
  cases access <;> simp [failureMessage, ErrorCalls.rejectionMessage, Runtime.function, Runtime.body,
    signature, Runtime.require, Runtime.instancePrefix, Runtime.reject, Runtime.branch, Runtime.fail,
    Runtime.ret, Runtime.scalarAccessCheck, Runtime.negate, Runtime.call, Runtime.v, Runtime.n,
    functionTexts, statementTexts, expressionTexts]

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ∈ sigs) (fresh : LiteralPreparation.KernelNamesFresh sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  intro before firstBlock signed
  obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
    (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" Logging.category_collected firstBlock
  have each : ∀ access, ∃ message, pool.addresses firstBlock (failureMessage access) = some message := by
    intro access
    exact LiteralPreparation.message_bound model sigs made signature member
      (failureMessage access) (failure_message_collected model access) firstBlock
  choose messages bound using each
  have categoryStored := pool.storage_valid before firstBlock signed "logStatus" category categoryBound
  have messageStored := fun access => pool.storage_valid before firstBlock signed _ (messages access) (bound access)
  refine ⟨category, messages, categoryBound, categoryStored, fun access => ⟨bound access, messageStored access⟩, ?_, ?_⟩
  · intro E program same
    have defined : (@CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program).definitions
        signature.name = some (.tree (Runtime.function model signature)) := by
      rw [same]
      exact LiteralPreparation.function_bound model sigs unique signature member
    have helper : (@CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program).definitions
        "fail" = some (.tree Runtime.helpers[0]) := by
      rw [same]
      exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])
    refine ⟨quiet_execution_correct (static := ⟨pool.addresses firstBlock⟩) model program _ defined ?_ ?_ ?_,
      fun access => silent_execution_correct (static := ⟨pool.addresses firstBlock⟩) model access program
        _ _ defined helper (bound access)⟩
    · rw [same]
      exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[1] (by simp [Runtime.helpers])
    · rw [same]
      exact LiteralPreparation.numerical_bound model sigs fresh .rhs
    · rw [same]
      exact LiteralPreparation.numerical_program model sigs
  · intro program same access
    apply failure_execution_correct (static := ⟨pool.addresses firstBlock⟩) model access program
      category (messages access) _ signed _ _ categoryBound (bound access) categoryStored (messageStored access)
    · rw [same]
      exact LiteralPreparation.function_bound model sigs unique signature member
    · rw [same]
      exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])

structure FunctionContract (model : Solve.FMI3Model source) (sigs : List Signature) (text helper : String) : Prop where
  member : signature ∈ sigs
  printed : text = (Runtime.function model signature).render
  tokenization : Printer.FunctionTokenization RuntimePrinter.typedefs text (Runtime.function model signature)
  numerical : ModelRhs.FunctionContract model sigs helper
  prepared : ∀ pool, LiteralPreparation.prepare model sigs = some pool → PreparedContract model sigs pool

theorem rendered_contract (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ∈ sigs) (fresh : LiteralPreparation.KernelNamesFresh sigs) :
    FunctionContract model sigs (Runtime.function model signature).render Runtime.helpers[1].render := by
  refine ⟨member, rfl, ?_, ModelRhs.rendered_contract model sigs fresh,
    fun _ made => prepared_correct model sigs unique member fresh made⟩
  apply RuntimePrinter.function_tokenization
  refine ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)),
    by decide +kernel, ?_⟩
  intro param member
  simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals exact ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩

end Rumoca.FMI3.DerivativeCalls

noncomputable section
namespace Rumoca.FMI3.DerivativeCalls
open CMemory
variable [interface : CInterface]

/-- The output contains the same derivative as Solve's ME view. Only the
output cell changes; preserving separate model storage needs its ordinary
non-aliasing premise. This getter does not advance time or select a solver. -/
theorem QuietExecutionContract.get_refines (contract : QuietExecutionContract model program heap)
    (p buffer : Address) (mode : Mode) (state : ModelExchange.State) (old : Option Value)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives .me mode)
    (storage : heap buffer = some ⟨.float64, true, old⟩) :
    ∃ after,
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling signature.name (values (some p) (some buffer) 1) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, after⟩) ∧
      load after buffer = some (.finite (ModelExchange.derivative model.solve state)) ∧
      (∀ address, address ≠ buffer → after address = heap address) ∧
      (StateProofs.stateAddress p ≠ buffer → StateProofs.Represents heap p state →
        StateProofs.Represents after p state) := by
  refine ⟨StateProofs.written heap buffer (Binary64.toBits (ModelExchange.derivative model.solve state)).val,
    contract.get p buffer mode state old hk hm allowed storage, ?_, ?_, ?_⟩
  · simp [StateProofs.written, load, convert, Value.finite]
  · intro address other
    exact StateProofs.written_frame heap buffer address _ other
  · intro separate represented
    simpa only [StateProofs.Represents, load,
      StateProofs.written_frame heap buffer (StateProofs.stateAddress p) _ separate] using represented

end Rumoca.FMI3.DerivativeCalls
