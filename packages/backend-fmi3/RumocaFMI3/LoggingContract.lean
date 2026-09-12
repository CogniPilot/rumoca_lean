import RumocaFMI3.Logging
import RumocaFMI3.RuntimePrinter
import RumocaFMI3.LiteralPreparation
import RumocaC.ObservedCalls
import XML.Syntax

/-! The emitted failure helper, its constructed category string and the actual
observable callback invocation share the same prepared definition table. All
represented host outcomes and disabled logging are required by the artifact
contract; the symbolic function binding and atomic host relation remain explicit. -/
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

/-- Every modeled callback choice, and the absence of outcomes, is covered. -/
def AllExecutionContract [interface : CInterface]
    (program : CCalls.Events.Program Invocation) (category : Address) (heap : Heap) (signed : Bool) : Prop :=
  ∀ (p message logger : Address) (environment : Option Address) (old : Option Value)
    (name text : String) (effect : ReturningEffect (signature name)),
    program.addresses logger = some name →
    program.externals name = some (External.observed (signature name) effect) →
    heap (p.member "mode") = some ⟨.int32, true, old⟩ →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    Stored signed heap message text →
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fail" [.pointer (some p), .pointer (some message)] heap .done) behavior ↔
      (∃ value after, effect.execute (arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after ∧
        behavior = .terminates [⟨name, arguments environment category message⟩] ⟨.integer 3, after⟩) ∨
      ((∀ value after, ¬ effect.execute (arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after) ∧ behavior = .wrong [])) ∧
    (∀ value after, effect.execute (arguments environment category message)
      (LifecycleBodies.writeMode heap p .terminated) value after →
      Stored signed after category "logStatus" ∧ Stored signed after message text)

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem all_execution_correct (program : CCalls.Events.Program Invocation) (category : Address)
    (heap : Heap) (signed : Bool)
    (defined : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (literal : static.addresses "logStatus" = some category)
    (stored : Stored signed heap category "logStatus") :
    AllExecutionContract program category heap signed := by
  intro p message logger environment old name text effect address external hm hl hg he messageStored
  have all := failure_all_behaviors program heap p message category logger environment old name
    (External.observed (signature name) effect) defined address external rfl literal hm hl hg he
  constructor
  · intro behavior
    exact (all behavior).trans (observed_choices effect _ _ (fun _ after => ⟨.integer 3, after⟩) behavior)
  · intro value after executed
    have successful := (all (.terminates [⟨name, arguments environment category message⟩] ⟨.integer 3, after⟩)).mpr
      (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := CCalls.Events.termination_preserves successful
    exact ⟨stored.preserved preserved, messageStored.preserved preserved⟩

end

/-- The earlier determined-outcome guarantee is a consequence of the full
choice contract, retaining the earlier API without a duplicate body proof. -/
theorem AllExecutionContract.determined [interface : CInterface]
    {program : @CCalls.Events.Program interface Invocation}
    {category : Address} {heap : Heap} {signed : Bool}
    (contract : @AllExecutionContract interface program category heap signed) :
    @ExecutionContract interface program category heap signed := by
  intro p message logger environment old name text effect after address external hm hl hg he messageStored
    executed unique
  obtain ⟨all, strings⟩ := contract p message logger environment old name text effect
    address external hm hl hg he messageStored
  refine ⟨?_, strings .void after executed⟩
  intro behavior
  rw [all behavior]
  constructor
  · rintro (⟨value, final, performed, observed⟩ | ⟨missing, observed⟩)
    · obtain ⟨_, same⟩ := unique value final performed
      exact same ▸ observed
    · exact False.elim (missing .void after executed)
  · rintro rfl
    exact Or.inl ⟨.void, after, executed, rfl⟩

section
variable [static : StaticLiterals]
private local instance determinedInterface : CInterface := cInterface static.addresses

theorem execution_correct (program : CCalls.Events.Program Invocation) (category : Address)
    (heap : Heap) (signed : Bool)
    (defined : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (literal : static.addresses "logStatus" = some category)
    (stored : Stored signed heap category "logStatus") :
    ExecutionContract program category heap signed :=
  AllExecutionContract.determined (all_execution_correct program category heap signed defined literal stored)

end

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

def AllPreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop :=
  ∀ (before : Heap) (firstBlock : Nat) (signed : Bool), ∃ category,
    pool.addresses firstBlock "logStatus" = some category ∧
    Stored signed (pool.install before firstBlock signed) category "logStatus" ∧
    ∀ program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) Invocation,
      @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) Invocation program =
        LiteralPreparation.program model sigs →
      @AllExecutionContract (cInterface (pool.addresses firstBlock)) program category
        (pool.install before firstBlock signed) signed

theorem category_collected : "logStatus" ∈ functionTexts Runtime.helpers[0] := by
  simp [Runtime.helpers, Runtime.log, Runtime.branch, Runtime.both, Runtime.field,
    Runtime.v, Runtime.ret, Runtime.setMode, Runtime.put, Runtime.mode, Runtime.n,
    functionTexts, statementTexts, expressionTexts]

theorem all_prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : AllPreparedContract model sigs pool := by
  intro before firstBlock signed
  obtain ⟨category, bound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
    (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" category_collected firstBlock
  have stored := pool.storage_valid before firstBlock signed "logStatus" category bound
  refine ⟨category, bound, stored, ?_⟩
  intro program same
  apply all_execution_correct (static := ⟨pool.addresses firstBlock⟩) program category _ signed _ bound stored
  rw [same]
  exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])

theorem AllPreparedContract.determined
    (contract : AllPreparedContract model sigs pool) : PreparedContract model sigs pool := by
  intro before firstBlock signed
  obtain ⟨category, bound, stored, all⟩ := contract before firstBlock signed
  refine ⟨category, bound, stored, ?_⟩
  intro program same
  exact AllExecutionContract.determined (interface := cInterface (pool.addresses firstBlock)) (all program same)

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool :=
  (all_prepared_correct model sigs made).determined

/-- The actual disabled helper in the eventful machine, with arbitrary unused
foreign bindings. No message address, callback outcome or string lookup is
assumed. The same constructed pool used by enabled logging is retained. -/
def SilentPreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop :=
  ∀ (before : Heap) (firstBlock : Nat) (signed : Bool) (E : Type)
    (program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) E),
    @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program =
      LiteralPreparation.program model sigs →
    ∀ (p message : Address) (old : Option Value) (logger : Option Address),
      pool.install before firstBlock signed (p.member "mode") = some ⟨.int32, true, old⟩ →
      load (pool.install before firstBlock signed) (p.member "logger") = some (.pointer logger) →
      load (pool.install before firstBlock signed) (p.member "logging") = some (.integer 0) →
      ∀ behavior, (@CCalls.Events.machine E (cInterface (pool.addresses firstBlock)) program).Behaves
        (.calling "fail" [.pointer (some p), .pointer (some message)]
          (pool.install before firstBlock signed) .done) behavior ↔
        behavior = .terminates [] ⟨.integer 3,
          LifecycleBodies.writeMode (pool.install before firstBlock signed) p .terminated⟩

theorem silent_prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) :
    SilentPreparedContract model sigs pool := by
  intro before firstBlock signed E program same p message old logger hm hl hg behavior
  apply failure_silent_behaviors (static := ⟨pool.addresses firstBlock⟩) program
    (pool.install before firstBlock signed) p message old logger _ hm hl hg behavior
  rw [same]
  exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])

structure FunctionContract (model : Solve.FMI3Model source) (sigs : List Signature) (text : String) : Prop where
  printed : text = Runtime.helpers[0].render
  tokenization : Printer.FunctionTokenization RuntimePrinter.typedefs text Runtime.helpers[0]
  prepared : ∀ pool, LiteralPreparation.prepare model sigs = some pool → PreparedContract model sigs pool
  all_prepared : ∀ pool, LiteralPreparation.prepare model sigs = some pool → AllPreparedContract model sigs pool
  silent_prepared : ∀ pool, LiteralPreparation.prepare model sigs = some pool → SilentPreparedContract model sigs pool

theorem rendered_contract (model : Solve.FMI3Model source) (sigs : List Signature) :
    FunctionContract model sigs Runtime.helpers[0].render := by
  refine ⟨rfl, ?_, fun _ made => prepared_correct model sigs made,
    fun _ made => all_prepared_correct model sigs made, fun pool _ => silent_prepared_correct model sigs pool⟩
  exact (Printer.function_denotes (RuntimePrinter.helpers_printable Runtime.helpers[0]
    (by simp [Runtime.helpers]))).tokenization

/-- Interpret the category in the independently denoted actual XML document. -/
def MetadataContract (metadata category : String) : Prop :=
  ∃ root categories entry : XML.Element, XML.Document root metadata ∧
    root.name = "fmiModelDescription" ∧ categories ∈ root.children ∧
    categories.name = "LogCategories" ∧ entry ∈ categories.children ∧
    entry.name = "Category" ∧ entry.attributes.lookup "name" = some category

theorem metadata_correct (model : Solve.FMI3Model source)
    (document : XML.Document (modelDescription model) metadata) : MetadataContract metadata "logStatus" := by
  refine ⟨modelDescription model, ⟨"LogCategories", [], [⟨"Category", [("name", "logStatus")], [], ""⟩], ""⟩,
    ⟨"Category", [("name", "logStatus")], [], ""⟩, document, rfl, ?_, rfl, by simp, rfl, rfl⟩
  simp [modelDescription]

end Rumoca.FMI3.Logging
