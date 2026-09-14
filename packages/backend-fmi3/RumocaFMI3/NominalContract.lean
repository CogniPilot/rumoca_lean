import RumocaFMI3.NominalEnvironment
import RumocaFMI3.LoggingContract

/-! One required contract for the emitted nominal query, its actual internal
table, constructed error strings, and every admitted successful or failing call. -/
noncomputable section
namespace Rumoca.FMI3.Nominals
open CTree CMemory CLiteral CCalls.Events


section
variable [static : StaticLiterals]
private local instance executionInterface : CInterface := cInterface static.addresses

theorem failure_execution_correct (model : Solve.FMI3Model source) (access : Bool)
    (program : CCalls.Events.Program Invocation) (category message : Address) (heap : Heap) (signed : Bool)
    (defined : program.internal.definitions ErrorCalls.nominalSignature.name =
      some (.tree (Runtime.function model ErrorCalls.nominalSignature)))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (literal : static.addresses "logStatus" = some category)
    (messageBound : static.addresses (failureMessage access) = some message)
    (categoryStored : Stored signed heap category "logStatus")
    (messageStored : Stored signed heap message (failureMessage access)) :
    FailureExecutionContract access program category message heap signed := by
  intro p logger environment buffer count kind mode name effect address external hk hm hl hg he rejected
  have all := failure_all_behaviors model access program heap p message category logger
    environment buffer count kind mode name (External.observed (Logging.signature name) effect)
    defined helper messageBound address external rfl literal hk hm hl hg he rejected
  constructor
  · intro behavior
    exact (all behavior).trans (observed_choices effect _ _ (fun _ after => ⟨.integer 3, after⟩) behavior)
  · intro value after executed
    have successful := (all (.terminates [⟨name, Logging.arguments environment category message⟩] ⟨.integer 3, after⟩)).mpr
      (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := CCalls.Events.termination_preserves successful
    exact ⟨categoryStored.preserved preserved, messageStored.preserved preserved⟩

end


def SilentExecutionContract [interface : CInterface] (access : Bool) (program : CCalls.Events.Program E)
    (heap : Heap) : Prop :=
  ∀ p buffer count kind mode logger,
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (.integer 0) →
    FailureCondition access kind mode buffer count →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling ErrorCalls.nominalSignature.name (ErrorCalls.nominalArguments p buffer count) heap .done)
      behavior ↔ behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

section
variable [static : StaticLiterals]
private local instance contractInterface : CInterface := cInterface static.addresses

theorem quiet_execution_correct (model : Solve.FMI3Model source)
    (program : CCalls.Events.Program E) (heap : Heap)
    (defined : program.internal.definitions ErrorCalls.nominalSignature.name =
      some (.tree (Runtime.function model ErrorCalls.nominalSignature))) : QuietExecutionContract program heap := by
  constructor
  · intro p buffer kind mode old hk hm allowed storage behavior
    exact call_behaviors model program heap p buffer kind mode old defined hk hm allowed storage behavior
  · intro buffer count behavior
    exact null_behaviors model program heap buffer count defined behavior

theorem silent_execution_correct (model : Solve.FMI3Model source) (access : Bool)
    (program : CCalls.Events.Program E) (message : Address) (heap : Heap)
    (defined : program.internal.definitions ErrorCalls.nominalSignature.name =
      some (.tree (Runtime.function model ErrorCalls.nominalSignature)))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses (failureMessage access) = some message) :
    SilentExecutionContract access program heap := by
  intro p buffer count kind mode logger hk hm hl hg condition behavior
  exact failure_silent_behaviors model access program heap p message buffer logger count kind mode
    defined helper messageBound hk hm hl hg condition behavior

end

/-- Each branch is mandatory for the same actual function table and constructed
category/messages. Header membership is proved separately by the fixed checker. -/
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
      @QuietExecutionContract E (cInterface (pool.addresses firstBlock)) program (pool.install before firstBlock signed) ∧
      ∀ access, @SilentExecutionContract E (cInterface (pool.addresses firstBlock)) access program
        (pool.install before firstBlock signed)) ∧
    (∀ program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) Invocation,
      @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) Invocation program =
        LiteralPreparation.program model sigs →
      ∀ access, @FailureExecutionContract (cInterface (pool.addresses firstBlock)) access program category (messages access)
        (pool.install before firstBlock signed) signed)

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : ErrorCalls.nominalSignature ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  intro before firstBlock signed
  obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
    (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" Logging.category_collected firstBlock
  have each : ∀ access, ∃ message, pool.addresses firstBlock (failureMessage access) = some message := by
    intro access
    exact LiteralPreparation.message_bound model sigs made _ member _ (failure_message_collected model access) firstBlock
  choose messages bound using each
  have categoryStored := pool.storage_valid before firstBlock signed "logStatus" category categoryBound
  have messageStored := fun access => pool.storage_valid before firstBlock signed _ (messages access) (bound access)
  refine ⟨category, messages, categoryBound, categoryStored, fun access => ⟨bound access, messageStored access⟩, ?_, ?_⟩
  · intro E program same
    have defined : (@CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program).definitions
        ErrorCalls.nominalSignature.name = some (.tree (Runtime.function model ErrorCalls.nominalSignature)) := by
      rw [same]
      exact LiteralPreparation.function_bound model sigs unique _ member
    have helper : (@CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program).definitions
        "fail" = some (.tree Runtime.helpers[0]) := by
      rw [same]
      exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])
    exact ⟨quiet_execution_correct (static := ⟨pool.addresses firstBlock⟩) model program _ defined,
      fun access => silent_execution_correct (static := ⟨pool.addresses firstBlock⟩) model access program _ _
        defined helper (bound access)⟩
  · intro program same access
    apply failure_execution_correct (static := ⟨pool.addresses firstBlock⟩) model access program category (messages access)
      _ signed _ _ categoryBound (bound access) categoryStored (messageStored access)
    · rw [same]
      exact LiteralPreparation.function_bound model sigs unique _ member
    · rw [same]
      exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])

structure FunctionContract (model : Solve.FMI3Model source) (sigs : List Signature) (text : String) : Prop where
  member : ErrorCalls.nominalSignature ∈ sigs
  printed : text = (Runtime.function model ErrorCalls.nominalSignature).render
  tokenization : Printer.FunctionTokenization RuntimePrinter.typedefs text
    (Runtime.function model ErrorCalls.nominalSignature)
  prepared : ∀ pool, LiteralPreparation.prepare model sigs = some pool → PreparedContract model sigs pool
  runtime : ∀ pool, LiteralPreparation.prepare model sigs = some pool →
    NominalEnvironment.PreparedContract model sigs pool

theorem rendered_contract (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : ErrorCalls.nominalSignature ∈ sigs) :
    FunctionContract model sigs (Runtime.function model ErrorCalls.nominalSignature).render := by
  refine ⟨member, rfl, ?_, fun _ made => prepared_correct model sigs unique member made,
    fun _ made => NominalEnvironment.prepared_correct model sigs unique member made⟩
  apply RuntimePrinter.function_tokenization
  refine ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)),
    by decide +kernel, ?_⟩
  intro param member
  simp only [ErrorCalls.nominalSignature, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals exact ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)),
    by decide +kernel⟩

end Rumoca.FMI3.Nominals
