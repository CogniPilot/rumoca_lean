import RumocaFMI3.AbsentVariableFailures
import RumocaFMI3.LiteralPreparation
import RumocaFMI3.RuntimePrinter

noncomputable section
namespace Rumoca.FMI3.AbsentVariables
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory CLiteral.Interface

theorem message_collected (model : Solve.FMI3Model source) (ty : VariableType) (write : Bool) (reason : Failure) :
    failureMessage reason ∈ functionTexts (Runtime.function model (signature ty write)) := by
  cases reason <;> simp [functionTexts, Runtime.function, body_eq, suffix, failureMessage,
    ErrorCalls.rejectionMessage,
    Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject,
    Runtime.branch, Runtime.fail, Runtime.ret, Runtime.call, Runtime.ok,
    statementTexts, expressionTexts, Runtime.v]

/-- Each family member uses the same prepared function table and literal pool.
The contracts remain valid after intervening calls preserve readonly storage. -/
structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (ty : VariableType) (write : Bool)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  quiet : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program E),
      program.internal = LiteralPreparation.program model sigs → QuietContract ty write program
  staticQuiet : ∀ (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := executionInterface objects (pool.addresses firstBlock)
    ∀ (program : Program E),
      program.internal = LiteralPreparation.program model sigs → QuietContract ty write program
  failures : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool)
    (objects : Objects) (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ (category : Address) (messages : Failure → Address),
      pool.addresses firstBlock "logStatus" = some category ∧
      (∀ reason, pool.addresses firstBlock (failureMessage reason) = some (messages reason)) ∧
      Stored signed heap category "logStatus" ∧ (∀ reason, Stored signed heap (messages reason) (failureMessage reason)) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : Program E),
         program.internal = LiteralPreparation.program model sigs → ∀ reason, SuppressedContract ty write reason program heap) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (program : Program Invocation),
         program.internal = LiteralPreparation.program model sigs →
         ∀ reason, LoggedContract ty write reason program category (messages reason) heap signed)

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (ty : VariableType) (write : Bool)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ty write ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs ty write pool := by
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro program actual
    apply quiet_correct header objects (pool.addresses firstBlock) model ty write program
    rw [actual]
    exact LiteralPreparation.function_bound model sigs unique (signature ty write) member
  · intro E objects firstBlock
    letI : CInterface := executionInterface objects (pool.addresses firstBlock)
    intro program actual
    apply quiet_static_correct objects (pool.addresses firstBlock) model ty write program
    rw [actual]
    exact LiteralPreparation.function_bound model sigs unique (signature ty write) member
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
      (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" Logging.category_collected firstBlock
    have available : ∀ reason, ∃ message, pool.addresses firstBlock (failureMessage reason) = some message := by
      intro reason
      exact LiteralPreparation.message_bound model sigs made (signature ty write) member
        (failureMessage reason) (message_collected model ty write reason) firstBlock
    choose messages messageBound using available
    have categoryStored := (pool.storage_valid before firstBlock signed "logStatus" category categoryBound).preserved frame
    have messageStored : ∀ reason, Stored signed heap (messages reason) (failureMessage reason) := fun reason =>
      (pool.storage_valid before firstBlock signed (failureMessage reason) (messages reason) (messageBound reason)).preserved frame
    let literals := pool.addresses firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    have definitions : ∀ (E : Type) (program : Program E),
        program.internal = LiteralPreparation.program model sigs →
        program.internal.definitions (signature ty write).name =
          some (.tree (Runtime.function model (signature ty write))) ∧
        program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
      intro E program actual
      constructor
      · rw [actual]; exact LiteralPreparation.function_bound model sigs unique (signature ty write) member
      · rw [actual]; exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])
    refine ⟨category, messages, categoryBound, messageBound, categoryStored, messageStored, ?_, ?_⟩
    · intro E program actual reason
      obtain ⟨defined, helper⟩ := definitions E program actual
      exact suppressed_correct header objects literals model ty write reason program (messages reason) heap defined helper (messageBound reason)
    · intro program actual reason
      obtain ⟨defined, helper⟩ := definitions Invocation program actual
      exact logged_correct header objects literals model ty write reason program category (messages reason) heap signed defined helper
        categoryBound (messageBound reason) categoryStored (messageStored reason)

theorem value_type_printable (ty : VariableType) (write : Bool) :
    Syntax.TypeSpelling RuntimePrinter.typedefs ((if write then "const fmi3" else "fmi3") ++ ty.name) := by
  have base : Syntax.TypeSpelling RuntimePrinter.typedefs ("fmi3" ++ ty.name) :=
    Syntax.TypeSpelling.named (.typedefName (by cases ty <;> decide +kernel) (by cases ty <;> decide +kernel))
  cases write with
  | false => exact base
  | true => exact Syntax.TypeSpelling.const base

theorem signature_printable (ty : VariableType) (write : Bool) :
    Printer.SignaturePrintable RuntimePrinter.typedefs (signature ty write) := by
  unfold Printer.SignaturePrintable
  dsimp only [signature]
  refine ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)),
    by cases ty <;> cases write <;> decide +kernel, ?_⟩
  rw [List.append_assoc, List.forall_mem_append]
  constructor
  · intro param member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals refine ⟨?_, by decide +kernel⟩
    all_goals first
      | exact Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel))
      | exact Syntax.TypeSpelling.const
          (show Syntax.TypeSpelling RuntimePrinter.typedefs "fmi3ValueReference" from
            Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)))
  · rw [List.forall_mem_append]
    constructor
    · intro param member
      split at member
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        subst param
        refine ⟨?_, by change CIdentifier.valid _ "valueSizes" = true; decide +kernel⟩
        cases write with
        | false => exact Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel))
        | true =>
          exact Syntax.TypeSpelling.const
            (show Syntax.TypeSpelling RuntimePrinter.typedefs "size_t" from
              Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)))
      · cases member
    · intro param member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨value_type_printable ty write, by change CIdentifier.valid _ "values" = true; decide +kernel⟩
      · exact ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩

structure FunctionContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (ty : VariableType) (write : Bool) (text : String) : Prop where
  member : signature ty write ∈ sigs
  printed : text = (Runtime.function model (signature ty write)).render
  tokenization : Printer.FunctionTokenization RuntimePrinter.typedefs text (Runtime.function model (signature ty write))
  prepared : ∀ pool, LiteralPreparation.prepare model sigs = some pool → PreparedContract model sigs ty write pool

theorem rendered_contract (model : Solve.FMI3Model source) (sigs : List Signature)
    (ty : VariableType) (write : Bool)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ty write ∈ sigs) :
    FunctionContract model sigs ty write (Runtime.function model (signature ty write)).render :=
  ⟨member, rfl, RuntimePrinter.function_tokenization model (signature ty write) (signature_printable ty write),
    fun _ made => prepared_correct model sigs ty write unique member made⟩

def FamilyContract (model : Solve.FMI3Model source) (sigs : List Signature) : Prop :=
  ∀ ty write, FunctionContract model sigs ty write (Runtime.function model (signature ty write)).render

theorem family_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (members : ∀ ty write, signature ty write ∈ sigs) : FamilyContract model sigs :=
  fun ty write => rendered_contract model sigs ty write unique (members ty write)

end Rumoca.FMI3.AbsentVariables
end
