import RumocaFMI3.InitializationQuiet
import RumocaFMI3.InitializationErrors
import RumocaFMI3.InitializationExitErrors

noncomputable section
namespace Rumoca.FMI3.InitializationCalls
open CTree CMemory CLiteral CCalls.Events

/-- Both complete public functions share one actual definition table and
installed literal pool. Quiet calls quantify over heaps, allowing composition
through writes by earlier certified calls. Failures retain the logger domain. -/
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
      @QuietExecutionContract E (cInterface (pool.addresses firstBlock)) program ∧
      (∀ reason, @SilentExecutionContract E (cInterface (pool.addresses firstBlock)) reason program
        (pool.install before firstBlock signed)) ∧
      @InitializationExit.SilentExecutionContract E (cInterface (pool.addresses firstBlock)) program
        (pool.install before firstBlock signed)) ∧
    (∀ program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) Invocation,
      @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) Invocation program =
        LiteralPreparation.program model sigs →
      (∀ reason, @FailureExecutionContract (cInterface (pool.addresses firstBlock)) reason program
        category (messages reason) (pool.install before firstBlock signed) signed) ∧
      @InitializationExit.FailureExecutionContract (cInterface (pool.addresses firstBlock)) program
        category (messages .lifecycle) (pool.install before firstBlock signed) signed)

/-- Quiet-call composition depends only on the prepared function table, so it
can be used after earlier writes without reconstructing a literal installation. -/
theorem PreparedContract.quiet (contract : PreparedContract model sigs pool) (firstBlock : Nat)
    (E : Type) (program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) E)
    (same : @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program =
      LiteralPreparation.program model sigs) :
    @QuietExecutionContract E (cInterface (pool.addresses firstBlock)) program := by
  obtain ⟨_, _, _, _, _, quiet, _⟩ := contract (fun _ => none) firstBlock false
  exact (quiet E program same).1

theorem failure_message_collected (model : Solve.FMI3Model source) (reason : Failure) :
    failureMessage reason ∈ functionTexts (Runtime.function model signature) := by
  rw [function_eq]
  cases reason <;> simp [failureMessage, message, ErrorCalls.rejectionMessage,
    function, code, tail, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard,
    Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, Runtime.call,
    Runtime.initialTime, Runtime.put, Runtime.setMode, Runtime.ok,
    functionTexts, statementTexts, expressionTexts]

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (enterMember : signature ∈ sigs) (exitMember : InitializationExit.signature ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  intro before firstBlock signed
  obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
    (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" Logging.category_collected firstBlock
  have each : ∀ reason, ∃ message, pool.addresses firstBlock (failureMessage reason) = some message := by
    intro reason
    exact LiteralPreparation.message_bound model sigs made signature enterMember
      (failureMessage reason) (failure_message_collected model reason) firstBlock
  choose messages bound using each
  have categoryStored := pool.storage_valid before firstBlock signed "logStatus" category categoryBound
  have messageStored := fun reason => pool.storage_valid before firstBlock signed _ (messages reason) (bound reason)
  refine ⟨category, messages, categoryBound, categoryStored,
    fun reason => ⟨bound reason, messageStored reason⟩, ?_, ?_⟩
  · intro E program same
    have enterDefined : (@CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program).definitions
        signature.name = some (.tree function) := by
      rw [same, ← function_eq model]
      exact LiteralPreparation.function_bound model sigs unique signature enterMember
    have exitDefined : (@CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program).definitions
        InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) := by
      rw [same]
      exact LiteralPreparation.function_bound model sigs unique InitializationExit.signature exitMember
    have helper : (@CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program).definitions
        "fail" = some (.tree Runtime.helpers[0]) := by
      rw [same]
      exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])
    exact ⟨quiet_execution_correct (static := ⟨pool.addresses firstBlock⟩) model program enterDefined exitDefined,
      fun reason => silent_execution_correct (static := ⟨pool.addresses firstBlock⟩) reason program
        _ _ enterDefined helper (bound reason),
      InitializationExit.silent_execution_correct (static := ⟨pool.addresses firstBlock⟩) model program
        _ _ exitDefined helper (bound .lifecycle)⟩
  · intro program same
    have enterDefined : (@CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) Invocation program).definitions
        signature.name = some (.tree function) := by
      rw [same, ← function_eq model]
      exact LiteralPreparation.function_bound model sigs unique signature enterMember
    have exitDefined : (@CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) Invocation program).definitions
        InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) := by
      rw [same]
      exact LiteralPreparation.function_bound model sigs unique InitializationExit.signature exitMember
    have helper : (@CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) Invocation program).definitions
        "fail" = some (.tree Runtime.helpers[0]) := by
      rw [same]
      exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])
    exact ⟨fun reason => failure_execution_correct (static := ⟨pool.addresses firstBlock⟩) reason program
        category (messages reason) _ signed enterDefined helper categoryBound (bound reason)
        categoryStored (messageStored reason),
      InitializationExit.failure_execution_correct (static := ⟨pool.addresses firstBlock⟩) model program
        category (messages .lifecycle) _ signed exitDefined helper categoryBound (bound .lifecycle)
        categoryStored (messageStored .lifecycle)⟩

structure FunctionContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (enterText exitText : String) : Prop where
  enterMember : signature ∈ sigs
  exitMember : InitializationExit.signature ∈ sigs
  enterPrinted : enterText = (Runtime.function model signature).render
  exitPrinted : exitText = (Runtime.function model InitializationExit.signature).render
  enterTokenization : Printer.FunctionTokenization RuntimePrinter.typedefs enterText (Runtime.function model signature)
  exitTokenization : Printer.FunctionTokenization RuntimePrinter.typedefs exitText
    (Runtime.function model InitializationExit.signature)
  prepared : ∀ pool, LiteralPreparation.prepare model sigs = some pool → PreparedContract model sigs pool

theorem rendered_contract (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (enterMember : signature ∈ sigs) (exitMember : InitializationExit.signature ∈ sigs) :
    FunctionContract model sigs (Runtime.function model signature).render
      (Runtime.function model InitializationExit.signature).render := by
  refine ⟨enterMember, exitMember, rfl, rfl, ?_, ?_, fun _ made =>
    prepared_correct model sigs unique enterMember exitMember made⟩
  · apply RuntimePrinter.function_tokenization
    refine ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)),
      by decide +kernel, ?_⟩
    intro param member
    simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩
  · apply RuntimePrinter.function_tokenization
    refine ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)),
      by decide +kernel, ?_⟩
    intro param member
    simp only [InitializationExit.signature, List.mem_cons, List.not_mem_nil, or_false] at member
    subst param
    exact ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩

end Rumoca.FMI3.InitializationCalls
