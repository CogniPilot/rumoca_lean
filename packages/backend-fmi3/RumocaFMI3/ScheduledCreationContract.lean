import RumocaFMI3.ScheduledCreation
import RumocaFMI3.LiteralPreparation
import RumocaFMI3.RuntimePrinter
import RumocaC.PrinterCertificate
import Lean

noncomputable section
namespace Rumoca.FMI3.ScheduledCreation
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory CLiteral.Interface

theorem message_collected (model : Solve.FMI3Model source) :
    message ∈ functionTexts (Runtime.function model signature) := by
  simp [functionTexts, Runtime.function, body, FactoryRejection.code, FactoryRejection.logCall,
    message, statementTexts, expressionTexts]

structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  quiet : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program E), program.internal = LiteralPreparation.program model sigs →
      ∀ (args : Raw) (heap : Heap), (args.logger.isSome && args.logging) = false →
      ∀ observed, (machine program).Behaves (.calling signature.name args.values heap .done) observed ↔
        observed = .terminates [] ⟨.pointer none, heap⟩
  logged : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool)
    (objects : Objects) (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ category text,
      pool.addresses firstBlock "logStatus" = some category ∧
      pool.addresses firstBlock message = some text ∧
      Stored signed heap category "logStatus" ∧ Stored signed heap text message ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : Program E), program.internal = LiteralPreparation.program model sigs →
       ∀ (args : Raw) (logger : Address) (name : String) (foreign : External E),
         args.logger = some logger → args.logging = true →
         program.addresses logger = some name → program.externals name = some foreign →
         foreign.signature = Logging.signature name →
         (∀ observed, (machine program).Behaves (.calling signature.name args.values heap .done) observed ↔
           (∃ events value after, foreign.execute (Logging.arguments args.environment category text)
             heap events value after ∧ observed = .terminates events ⟨.pointer none, after⟩) ∨
           ((∀ events value after, ¬ foreign.execute (Logging.arguments args.environment category text)
             heap events value after) ∧ observed = .wrong [])) ∧
         (∀ events value after, foreign.execute (Logging.arguments args.environment category text)
           heap events value after → Stored signed after category "logStatus" ∧ Stored signed after text message))

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro program actual args heap quiet observed
    apply quiet_call header objects (pool.addresses firstBlock) model args program heap
    · rw [actual]; exact LiteralPreparation.function_bound model sigs unique signature member
    · exact quiet
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
      (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" Logging.category_collected firstBlock
    obtain ⟨text, bound⟩ := LiteralPreparation.message_bound model sigs made signature member
      message (message_collected model) firstBlock
    have categoryStored := (pool.storage_valid before firstBlock signed "logStatus" category categoryBound).preserved frame
    have textStored := (pool.storage_valid before firstBlock signed message text bound).preserved frame
    refine ⟨category, text, categoryBound, bound, categoryStored, textStored, ?_⟩
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro E program actual args logger name foreign loggerBound logging address external prototype
    have defined : program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) := by
      rw [actual]; exact LiteralPreparation.function_bound model sigs unique signature member
    refine ⟨logged_call header objects (pool.addresses firstBlock) model args program heap logger category text
      name foreign defined loggerBound logging categoryBound bound address external prototype, ?_⟩
    intro events value after executed
    have preserved := foreign.readonly _ _ _ _ _ executed
    exact ⟨categoryStored.preserved preserved, textStored.preserved preserved⟩

open Lean Elab Command in
run_cmd do
  let proof ← CTree.Printer.Certificate.signatureProof (← `(term| RuntimePrinter.typedefs)) signature
  let theoremName := mkIdent `_root_.Rumoca.FMI3.ScheduledCreation.signature_printable
  elabCommand (← `(command| theorem $theoremName:ident :
    CTree.Printer.SignaturePrintable RuntimePrinter.typedefs signature := $proof))

structure FunctionContract (model : Solve.FMI3Model source) (sigs : List Signature) (text : String) : Prop where
  member : signature ∈ sigs
  printed : text = (Runtime.function model signature).render
  tokenization : Printer.FunctionTokenization RuntimePrinter.typedefs text (Runtime.function model signature)
  fragment : ∃ before after, Runtime.render model sigs = before ++ text ++ after
  prepared : ∀ pool, LiteralPreparation.prepare model sigs = some pool → PreparedContract model sigs pool

theorem rendered_contract (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ∈ sigs) : FunctionContract model sigs (Runtime.function model signature).render :=
  ⟨member, rfl, RuntimePrinter.function_tokenization model signature signature_printable,
    LiteralPreparation.rendered_member model sigs signature member,
    fun _ made => prepared_correct model sigs unique member made⟩

end Rumoca.FMI3.ScheduledCreation
end

