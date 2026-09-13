import RumocaFMI3.DiscreteCalls

noncomputable section
namespace Rumoca.FMI3.DiscreteCalls
open CTree CMemory CBody StaticFactory CLiteral.Interface
open CLiteral CCalls.Events

theorem message_collected (model : Solve.FMI3Model source) (reason : Failure) :
    message reason ∈ functionTexts (Runtime.function model signature) := by
  cases reason <;>
    simp [functionTexts, Runtime.function, body, Runtime.require, Runtime.instancePrefix,
      Runtime.modeGuard, Runtime.pointerCheck, Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret,
      Runtime.call, Runtime.ok, ErrorCalls.rejectionMessage, message, tail, names, layouts,
      Runtime.out, Runtime.v, statementTexts, expressionTexts]

structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  quiet : ∀ (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := executionInterface objects (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model sigs → QuietContract program
  failures : ∀ (before : Heap) (firstBlock : Nat) (signed : Bool) (objects : Objects)
    (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ category messages,
      pool.addresses firstBlock "logStatus" = some category ∧
      (∀ reason, pool.addresses firstBlock (message reason) = some (messages reason)) ∧
      Stored signed heap category "logStatus" ∧
      (∀ reason, Stored signed heap (messages reason) (message reason)) ∧
      (letI : CInterface := executionInterface objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : CCalls.Events.Program E),
         program.internal = LiteralPreparation.program model sigs → SuppressedContract program heap) ∧
      (letI : CInterface := executionInterface objects (pool.addresses firstBlock)
       ∀ (program : CCalls.Events.Program Invocation),
         program.internal = LiteralPreparation.program model sigs → LoggedContract program category messages heap signed)

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  constructor
  · intro E objects firstBlock
    letI : CInterface := executionInterface objects (pool.addresses firstBlock)
    intro program actual
    apply quiet_correct objects (pool.addresses firstBlock) model program
    rw [actual]
    exact LiteralPreparation.function_bound model sigs unique signature member
  · intro before firstBlock signed objects heap frame
    obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
      (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" Logging.category_collected firstBlock
    have allMessages : ∀ reason, ∃ address, pool.addresses firstBlock (message reason) = some address := by
      intro reason
      exact LiteralPreparation.message_bound model sigs made signature member
        (message reason) (message_collected model reason) firstBlock
    let messages : Failure → Address := fun reason => Classical.choose (allMessages reason)
    have messageBound : ∀ reason, pool.addresses firstBlock (message reason) = some (messages reason) :=
      fun reason => Classical.choose_spec (allMessages reason)
    have categoryStored := (pool.storage_valid before firstBlock signed "logStatus" category categoryBound).preserved frame
    have messageStored : ∀ reason, Stored signed heap (messages reason) (message reason) := fun reason =>
      (pool.storage_valid before firstBlock signed (message reason) (messages reason) (messageBound reason)).preserved frame
    let literals := pool.addresses firstBlock
    letI : CInterface := executionInterface objects literals
    have definitions : ∀ (E : Type) (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program model sigs →
        program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) ∧
        program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
      intro E program actual
      constructor
      · rw [actual]; exact LiteralPreparation.function_bound model sigs unique signature member
      · rw [actual]; exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])
    refine ⟨category, messages, categoryBound, messageBound, categoryStored, messageStored, ?_, ?_⟩
    · intro E program actual
      obtain ⟨defined, helper⟩ := definitions E program actual
      exact suppressed_correct objects literals model program messages heap defined helper messageBound
    · intro program actual
      obtain ⟨defined, helper⟩ := definitions Invocation program actual
      exact logged_correct objects literals model program category messages heap signed defined helper
        categoryBound messageBound categoryStored messageStored

/-- Exact public signature and independently tokenized function bytes, with
all represented call cases tied to the actual literal pool and function table. -/
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
  intro param member
  simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩
  · exact ⟨Syntax.TypeSpelling.pointer (text := "fmi3Boolean") (.named (.typedefName (by decide +kernel) (by decide +kernel))), by decide +kernel⟩
  · exact ⟨Syntax.TypeSpelling.pointer (text := "fmi3Boolean") (.named (.typedefName (by decide +kernel) (by decide +kernel))), by decide +kernel⟩
  · exact ⟨Syntax.TypeSpelling.pointer (text := "fmi3Boolean") (.named (.typedefName (by decide +kernel) (by decide +kernel))), by decide +kernel⟩
  · exact ⟨Syntax.TypeSpelling.pointer (text := "fmi3Boolean") (.named (.typedefName (by decide +kernel) (by decide +kernel))), by decide +kernel⟩
  · exact ⟨Syntax.TypeSpelling.pointer (text := "fmi3Boolean") (.named (.typedefName (by decide +kernel) (by decide +kernel))), by decide +kernel⟩
  · exact ⟨Syntax.TypeSpelling.pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel))), by decide +kernel⟩

end Rumoca.FMI3.DiscreteCalls
