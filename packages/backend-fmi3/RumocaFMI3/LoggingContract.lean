import RumocaFMI3.Logging
import RumocaFMI3.RuntimePrinter
import RumocaFMI3.LiteralPreparation
import RumocaC.ObservedCalls
import XML.Syntax

/-! The emitted failure helper, its constructed category string and the actual
observable callback invocation share the same prepared definition table. The
importer's returning effect and symbolic function binding remain explicit. -/
noncomputable section
namespace Rumoca.FMI3.Logging
open CTree CMemory CLiteral CCalls.Events

/-- Admissible returning-host executions of the actual helper. The callback is
observed with its converted arguments; its writable effects are retained. -/
def ExecutionContract [interface : CInterface] (program : CCalls.Events.Program Invocation) (category : Address)
    (heap : Heap) (signed : Bool) : Prop :=
  ∀ (p message logger : Address) (environment : Option Address) (old : Option Value)
    (name text : String) (effect : ReturningEffect (signature name)) (after : Heap),
    program.addresses logger = some name →
    program.externals name = some (External.observed (signature name) effect) →
    heap (p.member "mode") = some ⟨.int32, true, old⟩ →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    Stored signed heap message text →
    effect.execute (arguments environment category message)
      (LifecycleBodies.writeMode heap p .terminated) .void after →
    (∀ value out, effect.execute (arguments environment category message)
      (LifecycleBodies.writeMode heap p .terminated) value out → value = .void ∧ out = after) →
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fail" [.pointer (some p), .pointer (some message)] heap .done) behavior ↔
      behavior = .terminates [⟨name, arguments environment category message⟩] ⟨.integer 3, after⟩) ∧
    Stored signed after category "logStatus" ∧ Stored signed after message text

variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem execution_correct (program : CCalls.Events.Program Invocation) (category : Address)
    (heap : Heap) (signed : Bool)
    (defined : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (literal : static.addresses "logStatus" = some category)
    (stored : Stored signed heap category "logStatus") :
    ExecutionContract program category heap signed := by
  intro p message logger environment old name text effect after address external hm hl hg he messageStored
    executed unique
  have behavior := failure_behaviors program heap after p message category logger environment old name
    (External.observed (signature name) effect) [⟨name, arguments environment category message⟩]
    defined address external rfl literal hm hl hg he ⟨rfl, executed⟩ (observed_unique effect unique)
  have preserved := CCalls.Events.termination_preserves
    ((behavior (.terminates [⟨name, arguments environment category message⟩] ⟨.integer 3, after⟩)).mpr rfl)
  exact ⟨behavior, stored.preserved preserved, messageStored.preserved preserved⟩

omit static in
def PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop :=
  ∀ (before : Heap) (firstBlock : Nat) (signed : Bool), ∃ category,
    pool.addresses firstBlock "logStatus" = some category ∧
    Stored signed (pool.install before firstBlock signed) category "logStatus" ∧
    ∀ program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) Invocation,
      @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) Invocation program =
        LiteralPreparation.program model sigs →
      @ExecutionContract (cInterface (pool.addresses firstBlock)) program category
        (pool.install before firstBlock signed) signed

omit static in
theorem category_collected : "logStatus" ∈ functionTexts Runtime.helpers[0] := by
  simp [Runtime.helpers, Runtime.log, Runtime.branch, Runtime.both, Runtime.field,
    Runtime.v, Runtime.ret, Runtime.setMode, Runtime.put, Runtime.mode, Runtime.n,
    functionTexts, statementTexts, expressionTexts]

omit static in
theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  intro before firstBlock signed
  obtain ⟨category, bound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
    (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" category_collected firstBlock
  have stored := pool.storage_valid before firstBlock signed "logStatus" category bound
  refine ⟨category, bound, stored, ?_⟩
  intro program same
  apply execution_correct (static := ⟨pool.addresses firstBlock⟩) program category _ signed
    _ bound stored
  rw [same]
  exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])

omit static in
structure FunctionContract (model : Solve.FMI3Model source) (sigs : List Signature) (text : String) : Prop where
  printed : text = Runtime.helpers[0].render
  tokenization : Printer.FunctionTokenization RuntimePrinter.typedefs text Runtime.helpers[0]
  prepared : ∀ pool, LiteralPreparation.prepare model sigs = some pool → PreparedContract model sigs pool

omit static in
theorem rendered_contract (model : Solve.FMI3Model source) (sigs : List Signature) :
    FunctionContract model sigs Runtime.helpers[0].render := by
  refine ⟨rfl, ?_, fun _ made => prepared_correct model sigs made⟩
  exact (Printer.function_denotes (RuntimePrinter.helpers_printable Runtime.helpers[0]
    (by simp [Runtime.helpers]))).tokenization

/-- Interpret the category in the independently denoted actual XML document. -/
def MetadataContract (metadata category : String) : Prop :=
  ∃ root categories entry : XML.Element, XML.Document root metadata ∧
    root.name = "fmiModelDescription" ∧ categories ∈ root.children ∧
    categories.name = "LogCategories" ∧ entry ∈ categories.children ∧
    entry.name = "Category" ∧ entry.attributes.lookup "name" = some category

omit static in
theorem metadata_correct (model : Solve.FMI3Model source)
    (document : XML.Document (modelDescription model) metadata) : MetadataContract metadata "logStatus" := by
  refine ⟨modelDescription model, ⟨"LogCategories", [], [⟨"Category", [("name", "logStatus")], [], ""⟩], ""⟩,
    ⟨"Category", [("name", "logStatus")], [], ""⟩, document, rfl, ?_, rfl, by simp, rfl, rfl⟩
  simp [modelDescription]

end Rumoca.FMI3.Logging
