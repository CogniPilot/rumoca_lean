import RumocaFMI3.CapabilityRejection
import RumocaFMI3.LiteralPreparation
import RumocaFMI3.RuntimePrinter

/-! Compositional contract for the actual generic rejection function. The
signature profile, body routing and independent printer premises remain
explicit until the public API inventory discharges them. No legal FMI call
domain or whole-translation-unit claim is inferred from defensive execution. -/
noncomputable section
namespace Rumoca.FMI3.CapabilityRejection
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory CLiteral.Interface

def NullContract [CInterface] (sig : Signature) (tail : List Parameter)
    (literals : CLiteralAddresses) (program : Program E) : Prop :=
  ∀ (inputs outputs : List Value),
    @CCalls.Signature.Arguments (cInterface literals) tail inputs outputs →
    ∀ heap observed, (machine program).Behaves
      (.calling sig.name (.pointer none :: inputs) heap .done) observed ↔
      observed = .terminates [] ⟨.integer 3, heap⟩

structure FailureContract [CInterface] (sig : Signature) (tail : List Parameter)
    (literals : CLiteralAddresses) (program : Program E) (heap : Heap)
    (category text : Address) (signed : Bool) : Prop where
  suppressed : ∀ (inputs outputs : List Value),
    @CCalls.Signature.Arguments (cInterface literals) tail inputs outputs →
    ∀ (p : Address) (old : Option Value) (logger : Option Address) (logging : Bool),
      heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) →
      ∀ observed, (machine program).Behaves
        (.calling sig.name (.pointer (some p) :: inputs) heap .done) observed ↔
        observed = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩
  logged : ∀ (inputs outputs : List Value),
    @CCalls.Signature.Arguments (cInterface literals) tail inputs outputs →
    ∀ (p logger : Address) (old : Option Value) (environment : Option Address)
      (name : String) (foreign : External E),
      program.addresses logger = some name → program.externals name = some foreign →
      foreign.signature = Logging.signature name →
      heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) →
      (∀ observed, (machine program).Behaves
        (.calling sig.name (.pointer (some p) :: inputs) heap .done) observed ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category text)
          (LifecycleBodies.writeMode heap p .terminated) events value after ∧
          observed = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category text)
          (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ observed = .wrong [])) ∧
      (∀ events value after, foreign.execute (Logging.arguments environment category text)
        (LifecycleBodies.writeMode heap p .terminated) events value after →
        Stored signed after category "logStatus" ∧ Stored signed after text message)

theorem failures_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (profile : Profile sig tail)
    (routed : Runtime.body model sig = code) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : Program E) (heap : Heap) (category text : Address) (signed : Bool),
      program.internal.definitions sig.name = some (.tree (Runtime.function model sig)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals message = some text → literals "logStatus" = some category →
      Stored signed heap category "logStatus" → Stored signed heap text message →
      FailureContract sig tail literals program heap category text signed := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap category text signed defined helper bound categoryBound categoryStored textStored
  constructor
  · intro inputs outputs arguments p old logger logging hm hl hg suppressed observed
    exact suppressed_call header objects literals model profile routed arguments program heap p text old logger logging
      defined helper bound hm hl hg suppressed observed
  · intro inputs outputs arguments p logger old environment name foreign address external prototype hm hl hg he
    have all := logged_call header objects literals model profile routed arguments program heap p text category logger
      old environment name foreign defined helper bound categoryBound address external prototype hm hl hg he
    refine ⟨all, ?_⟩
    intro events value after executed
    have completed := (all (.terminates events ⟨.integer 3, after⟩)).mpr
      (Or.inl ⟨events, value, after, executed, rfl⟩)
    have frame := CCalls.Events.termination_preserves completed
    exact ⟨categoryStored.preserved frame, textStored.preserved frame⟩

theorem message_collected (model : Solve.FMI3Model source)
    (routed : Runtime.body model sig = code) :
    message ∈ functionTexts (Runtime.function model sig) := by
  simp [functionTexts, Runtime.function, routed, code, message,
    Runtime.instancePrefix, Runtime.fail, Runtime.branch, Runtime.ret, Runtime.call,
    statementTexts, expressionTexts, Runtime.v]

structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (sig : Signature) (tail : List Parameter)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  null : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program E), program.internal = LiteralPreparation.program model sigs →
      NullContract sig tail (pool.addresses firstBlock) program
  failures : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool)
    (objects : Objects) (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ category text,
      pool.addresses firstBlock "logStatus" = some category ∧
      pool.addresses firstBlock message = some text ∧
      Stored signed heap category "logStatus" ∧ Stored signed heap text message ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : Program E), program.internal = LiteralPreparation.program model sigs →
         FailureContract sig tail (pool.addresses firstBlock) program heap category text signed)

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (profile : Profile sig tail) (routed : Runtime.body model sig = code)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : sig ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs sig tail pool := by
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro program actual inputs outputs arguments heap observed
    apply null_call header objects (pool.addresses firstBlock) model profile routed arguments program heap
    rw [actual]
    exact LiteralPreparation.function_bound model sigs unique sig member
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
      (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" Logging.category_collected firstBlock
    obtain ⟨text, bound⟩ := LiteralPreparation.message_bound model sigs made sig member
      message (message_collected model routed) firstBlock
    have categoryStored := (pool.storage_valid before firstBlock signed "logStatus" category categoryBound).preserved frame
    have textStored := (pool.storage_valid before firstBlock signed message text bound).preserved frame
    refine ⟨category, text, categoryBound, bound, categoryStored, textStored, ?_⟩
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro E program actual
    apply failures_correct header objects (pool.addresses firstBlock) model profile routed program heap category text signed
    · rw [actual]; exact LiteralPreparation.function_bound model sigs unique sig member
    · rw [actual]; exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])
    · exact bound
    · exact categoryBound
    · exact categoryStored
    · exact textStored

structure FunctionContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (sig : Signature) (tail : List Parameter) (text : String) : Prop where
  member : sig ∈ sigs
  profile : Profile sig tail
  printed : text = (Runtime.function model sig).render
  tokenization : Printer.FunctionTokenization RuntimePrinter.typedefs text (Runtime.function model sig)
  fragment : ∃ before after, Runtime.render model sigs = before ++ text ++ after
  prepared : ∀ pool, LiteralPreparation.prepare model sigs = some pool → PreparedContract model sigs sig tail pool

theorem rendered_contract (model : Solve.FMI3Model source) (sigs : List Signature)
    (profile : Profile sig tail) (routed : Runtime.body model sig = code)
    (printable : Printer.SignaturePrintable RuntimePrinter.typedefs sig)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : sig ∈ sigs) :
    FunctionContract model sigs sig tail (Runtime.function model sig).render :=
  ⟨member, profile, rfl, RuntimePrinter.function_tokenization model sig printable,
    LiteralPreparation.rendered_member model sigs sig member,
    fun _ made => prepared_correct model sigs profile routed unique member made⟩

end Rumoca.FMI3.CapabilityRejection
end

