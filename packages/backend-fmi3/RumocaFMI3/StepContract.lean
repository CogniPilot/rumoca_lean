import RumocaFMI3.StepCalls

/-! Mandatory-ready CS function contract: complete call cases, independent
function tokenization, and the actual prepared literals and numerical kernel. -/
noncomputable section
namespace Rumoca.FMI3.StepCalls
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem message_collected (model : Solve.FMI3Model source) (reason : StepRejections.Reason) :
    reason.message ∈ functionTexts (Runtime.function model StepEntry.signature) := by
  cases reason <;>
    simp [StepRejections.Reason.message, functionTexts, Runtime.function, StepEntry.body, StepEntry.outputCode, StepEntry.inputGuard,
      Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject, Runtime.branch,
      Runtime.fail, Runtime.ret, Runtime.call, Runtime.doStep,
      Runtime.stepRounding, Runtime.stepClock, Runtime.stepGrid, Runtime.stepDiscard, Runtime.log,
      Runtime.out, Runtime.pointerCheck, StepArguments.inputMessage, StepFailures.roundingMessage,
      StepFailures.stopMessage, StepDiscard.message, ErrorCalls.rejectionMessage,
      statementTexts, expressionTexts]

structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  quiet : ∀ (query : StepCases.Query) (objects : Objects) (firstBlock : Nat),
    NullContract query objects (pool.addresses firstBlock) model sigs ∧
    AcceptedContract query objects (pool.addresses firstBlock) model sigs
  rejections : ∀ (query : StepCases.Query) (before : Heap) (firstBlock : Nat) (signed : Bool)
    (objects : Objects) (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ category messages,
      pool.addresses firstBlock "logStatus" = some category ∧
      (∀ reason, pool.addresses firstBlock reason.message = some (messages reason)) ∧
      Stored signed heap category "logStatus" ∧
      (∀ reason, Stored signed heap (messages reason) reason.message) ∧
      SuppressedContract query objects (pool.addresses firstBlock) model sigs heap ∧
      LoggedContract query objects (pool.addresses firstBlock) model sigs heap signed category messages

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (fresh : LiteralPreparation.KernelNamesFresh sigs) (member : StepEntry.signature ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  constructor
  · intro query objects firstBlock
    exact ⟨null_correct query objects (pool.addresses firstBlock) model sigs unique member,
      accepted_correct query objects (pool.addresses firstBlock) model sigs unique fresh member⟩
  · intro query before firstBlock signed objects heap frame
    obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
      (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" Logging.category_collected firstBlock
    have allMessages : ∀ reason : StepRejections.Reason,
        ∃ address, pool.addresses firstBlock reason.message = some address := by
      intro reason
      exact LiteralPreparation.message_bound model sigs made StepEntry.signature member
        reason.message (message_collected model reason) firstBlock
    let messages : StepRejections.Reason → Address := fun reason => Classical.choose (allMessages reason)
    have messageBound : ∀ reason, pool.addresses firstBlock reason.message = some (messages reason) :=
      fun reason => Classical.choose_spec (allMessages reason)
    have categoryStored := (pool.storage_valid before firstBlock signed "logStatus" category categoryBound).preserved frame
    have messageStored : ∀ reason, Stored signed heap (messages reason) reason.message := fun reason =>
      (pool.storage_valid before firstBlock signed reason.message (messages reason) (messageBound reason)).preserved frame
    exact ⟨category, messages, categoryBound, messageBound, categoryStored, messageStored,
      suppressed_correct query objects (pool.addresses firstBlock) model sigs unique member heap messages messageBound,
      logged_correct query objects (pool.addresses firstBlock) model sigs unique member heap signed
        category messages categoryBound messageBound categoryStored messageStored⟩

/-- Complete public-call cases, independent function bytes, and prepared
literal/kernel bindings belong to one required artifact proposition. Header,
caller storage and foreign-effect boundaries remain explicit in its call fields. -/
structure FunctionContract (model : Solve.FMI3Model source) (sigs : List Signature) (text : String) : Prop where
  member : StepEntry.signature ∈ sigs
  printed : text = (Runtime.function model StepEntry.signature).render
  tokenization : Printer.FunctionTokenization RuntimePrinter.typedefs text (Runtime.function model StepEntry.signature)
  partition : ∀ query, ∃! outcome, StepCases.Condition query outcome
  cases : ∀ query, StepCases.Condition query .null ∨ StepCases.Condition query .accepted ∨
    ∃ reason : StepRejections.Reason, StepCases.Condition query reason.outcome
  logging : ∀ (logger : Option Address) (logging : Bool),
    (logger = none ∨ logging = false) ∨ ∃ address, logger = some address ∧ logging = true
  prepared : ∀ pool, LiteralPreparation.prepare model sigs = some pool → PreparedContract model sigs pool

theorem rendered_contract (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (fresh : LiteralPreparation.KernelNamesFresh sigs) (member : StepEntry.signature ∈ sigs) :
    FunctionContract model sigs (Runtime.function model StepEntry.signature).render := by
  refine ⟨member, rfl, ?_, StepCases.partition, outcome_cases, StaticErrors.logging_cases,
    fun _ made => prepared_correct model sigs unique fresh member made⟩
  apply RuntimePrinter.function_tokenization
  refine ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)),
    by decide +kernel, ?_⟩
  intro param member
  simp only [StepEntry.signature, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩
  · exact ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩
  · exact ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩
  · exact ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩
  · exact ⟨Syntax.TypeSpelling.pointer (text := "fmi3Boolean") (.named (.typedefName (by decide +kernel) (by decide +kernel))), by decide +kernel⟩
  · exact ⟨Syntax.TypeSpelling.pointer (text := "fmi3Boolean") (.named (.typedefName (by decide +kernel) (by decide +kernel))), by decide +kernel⟩
  · exact ⟨Syntax.TypeSpelling.pointer (text := "fmi3Boolean") (.named (.typedefName (by decide +kernel) (by decide +kernel))), by decide +kernel⟩
  · exact ⟨Syntax.TypeSpelling.pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel))), by decide +kernel⟩

end Rumoca.FMI3.StepCalls
end
