import RumocaFMI3.DiscreteEvaluationFailures

noncomputable section
namespace Rumoca.FMI3.DiscreteEvaluation
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory CLiteral.Interface

theorem message_collected (model : Solve.FMI3Model source) :
    ErrorCalls.rejectionMessage ∈ functionTexts (Runtime.function model signature) := by
  simp [functionTexts, Runtime.function, body, Runtime.require, Runtime.instancePrefix,
      Runtime.modeGuard, Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret,
      Runtime.call, Runtime.ok, ErrorCalls.rejectionMessage,
      statementTexts, expressionTexts, Runtime.v]

/-- Quiet calls are reusable on any valid later heap. Rejected calls share
the actual diagnostic pool, including after writes that preserve its storage. -/
structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  quiet : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model sigs → QuietContract program
  staticQuiet : ∀ (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := executionInterface objects (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model sigs → QuietContract program
  failures : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool) (objects : Objects)
    (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ category message,
      pool.addresses firstBlock "logStatus" = some category ∧
      pool.addresses firstBlock ErrorCalls.rejectionMessage = some message ∧
      Stored signed heap category "logStatus" ∧ Stored signed heap message ErrorCalls.rejectionMessage ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : CCalls.Events.Program E),
         program.internal = LiteralPreparation.program model sigs → SuppressedContract program heap) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (program : CCalls.Events.Program Invocation),
         program.internal = LiteralPreparation.program model sigs → LoggedContract program category message heap signed)

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro program actual
    apply quiet_correct header objects (pool.addresses firstBlock) model program
    rw [actual]
    exact LiteralPreparation.function_bound model sigs unique signature member
  · intro E objects firstBlock
    letI : CInterface := executionInterface objects (pool.addresses firstBlock)
    intro program actual
    apply quiet_static_correct objects (pool.addresses firstBlock) model program
    rw [actual]
    exact LiteralPreparation.function_bound model sigs unique signature member
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
      (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" Logging.category_collected firstBlock
    obtain ⟨message, messageBound⟩ := LiteralPreparation.message_bound model sigs made signature member
      ErrorCalls.rejectionMessage (message_collected model) firstBlock
    have categoryStored := (pool.storage_valid before firstBlock signed "logStatus" category categoryBound).preserved frame
    have messageStored := (pool.storage_valid before firstBlock signed ErrorCalls.rejectionMessage message messageBound).preserved frame
    let literals := pool.addresses firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    have definitions : ∀ (E : Type) (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program model sigs →
        program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) ∧
        program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
      intro E program actual
      constructor
      · rw [actual]; exact LiteralPreparation.function_bound model sigs unique signature member
      · rw [actual]; exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])
    refine ⟨category, message, categoryBound, messageBound, categoryStored, messageStored, ?_, ?_⟩
    · intro E program actual
      obtain ⟨defined, helper⟩ := definitions E program actual
      exact suppressed_correct header objects literals model program message heap defined helper messageBound
    · intro program actual
      obtain ⟨defined, helper⟩ := definitions Invocation program actual
      exact logged_correct header objects literals model program category message heap signed defined helper
        categoryBound messageBound categoryStored messageStored

/-- Required public signature, independent C tokenization and complete
represented call cases are bound to the same emitted function and pool. -/
structure FunctionContract (model : Solve.FMI3Model source) (sigs : List Signature) (text : String) : Prop where
  member : signature ∈ sigs
  printed : text = (Runtime.function model signature).render
  tokenization : Printer.FunctionTokenization RuntimePrinter.typedefs text (Runtime.function model signature)
  prepared : ∀ pool, LiteralPreparation.prepare model sigs = some pool → PreparedContract model sigs pool

theorem rendered_contract (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ∈ sigs) : FunctionContract model sigs (Runtime.function model signature).render := by
  refine ⟨member, rfl, ?_, fun _ made => prepared_correct model sigs unique member made⟩
  apply RuntimePrinter.function_tokenization
  refine ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)),
      by decide +kernel, ?_⟩
  all_goals
    intro param member
    simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
    subst param
    exact ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩

end Rumoca.FMI3.DiscreteEvaluation
