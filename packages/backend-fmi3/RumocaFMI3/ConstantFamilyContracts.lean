import RumocaFMI3.ConstantFunctions
import RumocaFMI3.AbsentVariableContract
import RumocaFMI3.CapabilityRejectionFamily

/-! The two unsupported/absent-type function families over the constant adapter
list. The family execution bodies are identical to the scalar renderer's; only
the surrounding function list (`ConstantFunctions.functions`) and its literal pool
differ. The model-agnostic execution core (`quiet_correct`, `suppressed_correct`,
`logged_correct`, `null_call`, `suppressed_call`, `logged_call`, `failures_correct`,
`quiet_call`, `logged_call`) is reused verbatim; the constant contracts only re-plumb
the definition-table and literal-pool facts from `ConstantFunctions`. No family
execution proof is duplicated.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and neither the scalar renderer, the families nor any
existing contract changes. -/
noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory CLiteral.Interface
open ConstantFunctions (constantFunction functions program prepare)

variable {source : AST.Model} {n : Nat}

/-! ### Bridging lemmas: fallthrough signatures render the scalar body -/

/-- Every absent-type family signature falls through the tensor dispatch to the
scalar body. -/
theorem absent_function (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (ty : AbsentVariables.VariableType) (write : Bool) :
    constantFunction model m (AbsentVariables.signature ty write)
      = Runtime.function model (AbsentVariables.signature ty write) := by
  cases ty <;> cases write <;> rfl

/-- Every unsupported-capability signature falls through the tensor dispatch to
the scalar body. -/
theorem capability_function (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n) :
    ∀ sig ∈ CapabilityRejection.signatures, constantFunction model m sig = Runtime.function model sig := by
  intro sig member
  fin_cases member <;> rfl

/-- `fmi3InstantiateScheduledExecution` falls through the tensor dispatch to the
scalar body. -/
theorem scheduled_function (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n) :
    constantFunction model m ScheduledCreation.signature
      = Runtime.function model ScheduledCreation.signature := rfl

/-- Definition-table fact for any signature that renders the scalar body. -/
theorem scalar_bound (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (sig : Signature) (member : sig ∈ sigs)
    (routed : constantFunction model m sig = Runtime.function model sig) :
    (program model m sigs).definitions sig.name = some (.tree (Runtime.function model sig)) := by
  rw [← routed]; exact ConstantFunctions.function_bound model m sigs unique sig member

/-- List membership of a scalar body rendered by the constant adapter list. -/
theorem scalar_member (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (sig : Signature) (member : sig ∈ sigs)
    (routed : constantFunction model m sig = Runtime.function model sig) :
    Runtime.function model sig ∈ functions model m sigs := by
  rw [← routed]; exact List.mem_append_right _ (List.mem_map.mpr ⟨sig, member, rfl⟩)

/-! ### Absent-type variable family over the constant adapter list -/

namespace ConstantAbsentVariables
open AbsentVariables

/-- The absent-type prepared contract over the constant adapter definition table
and literal pool. Same shape as the scalar `AbsentVariables.PreparedContract`,
but the function table is the constant adapter list's. -/
structure PreparedContract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (ty : VariableType) (write : Bool)
    (pool : Pool (LiteralPreparation.excluded ++ (functions model m sigs).flatMap functionNames)) : Prop where
  quiet : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (prog : Program E),
      prog.internal = program model m sigs → QuietContract ty write prog
  staticQuiet : ∀ (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := executionInterface objects (pool.addresses firstBlock)
    ∀ (prog : Program E),
      prog.internal = program model m sigs → QuietContract ty write prog
  failures : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool)
    (objects : Objects) (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ (category : Address) (messages : Failure → Address),
      pool.addresses firstBlock "logStatus" = some category ∧
      (∀ reason, pool.addresses firstBlock (failureMessage reason) = some (messages reason)) ∧
      Stored signed heap category "logStatus" ∧ (∀ reason, Stored signed heap (messages reason) (failureMessage reason)) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (prog : Program E),
         prog.internal = program model m sigs → ∀ reason, SuppressedContract ty write reason prog heap) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (prog : Program Invocation),
         prog.internal = program model m sigs →
         ∀ reason, LoggedContract ty write reason prog category (messages reason) heap signed)

theorem prepared_correct (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (ty : VariableType) (write : Bool)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ty write ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++ (functions model m sigs).flatMap functionNames)}
    (made : prepare model m sigs = some pool) : PreparedContract model m sigs ty write pool := by
  have routed := absent_function model m ty write
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro prog actual
    apply AbsentVariables.quiet_correct header objects (pool.addresses firstBlock) model ty write prog
    rw [actual]
    exact scalar_bound model m sigs unique (signature ty write) member routed
  · intro E objects firstBlock
    letI : CInterface := executionInterface objects (pool.addresses firstBlock)
    intro prog actual
    apply AbsentVariables.quiet_static_correct objects (pool.addresses firstBlock) model ty write prog
    rw [actual]
    exact scalar_bound model m sigs unique (signature ty write) member routed
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, categoryBound⟩ := ConstantFunctions.text_bound model m sigs made Runtime.helpers[0]
      (List.mem_append_left _ (by simp [ConstantFunctions.helpers, TensorFunctions.helpers])) "logStatus" Logging.category_collected firstBlock
    have available : ∀ reason, ∃ message, pool.addresses firstBlock (failureMessage reason) = some message := by
      intro reason
      exact ConstantFunctions.text_bound model m sigs made (Runtime.function model (signature ty write))
        (scalar_member model m sigs (signature ty write) member routed)
        (failureMessage reason) (AbsentVariables.message_collected model ty write reason) firstBlock
    choose messages messageBound using available
    have categoryStored := (pool.storage_valid before firstBlock signed "logStatus" category categoryBound).preserved frame
    have messageStored : ∀ reason, Stored signed heap (messages reason) (failureMessage reason) := fun reason =>
      (pool.storage_valid before firstBlock signed (failureMessage reason) (messages reason) (messageBound reason)).preserved frame
    let literals := pool.addresses firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    have definitions : ∀ (E : Type) (prog : Program E),
        prog.internal = program model m sigs →
        prog.internal.definitions (signature ty write).name =
          some (.tree (Runtime.function model (signature ty write))) ∧
        prog.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
      intro E prog actual
      refine ⟨?_, ?_⟩
      · rw [actual]; exact scalar_bound model m sigs unique (signature ty write) member routed
      · rw [actual]; exact ConstantFunctions.helpers_bound model m sigs Runtime.helpers[0] (by simp [ConstantFunctions.helpers, TensorFunctions.helpers])
    refine ⟨category, messages, categoryBound, messageBound, categoryStored, messageStored, ?_, ?_⟩
    · intro E prog actual reason
      obtain ⟨defined, helper⟩ := definitions E prog actual
      exact AbsentVariables.suppressed_correct header objects literals model ty write reason prog
        (messages reason) heap defined helper (messageBound reason)
    · intro prog actual reason
      obtain ⟨defined, helper⟩ := definitions Invocation prog actual
      exact AbsentVariables.logged_correct header objects literals model ty write reason prog category
        (messages reason) heap signed defined helper categoryBound (messageBound reason) categoryStored (messageStored reason)

structure FunctionContract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (ty : VariableType) (write : Bool) (text : String) : Prop where
  member : signature ty write ∈ sigs
  printed : text = (Runtime.function model (signature ty write)).render
  tokenization : Printer.FunctionTokenization RuntimePrinter.typedefs text (Runtime.function model (signature ty write))
  prepared : ∀ pool, prepare model m sigs = some pool → PreparedContract model m sigs ty write pool

theorem rendered_contract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (ty : VariableType) (write : Bool)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ty write ∈ sigs) :
    FunctionContract model m sigs ty write (Runtime.function model (signature ty write)).render :=
  ⟨member, rfl,
    RuntimePrinter.function_tokenization model (signature ty write) (AbsentVariables.signature_printable ty write),
    fun _ made => prepared_correct model m sigs ty write unique member made⟩

/-- The absent-type family contract over the constant adapter list. -/
def FamilyContract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) : Prop :=
  ∀ ty write, FunctionContract model m sigs ty write (Runtime.function model (signature ty write)).render

theorem family_correct (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (members : ∀ ty write, signature ty write ∈ sigs) : FamilyContract model m sigs :=
  fun ty write => rendered_contract model m sigs ty write unique (members ty write)

end ConstantAbsentVariables

/-! ### Unsupported-capability family over the constant adapter list -/

namespace ConstantCapabilityRejection
open CapabilityRejection

structure PreparedContract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (sig : Signature) (tail : List Parameter)
    (pool : Pool (LiteralPreparation.excluded ++ (functions model m sigs).flatMap functionNames)) : Prop where
  null : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (prog : Program E), prog.internal = program model m sigs →
      NullContract sig tail (pool.addresses firstBlock) prog
  failures : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool)
    (objects : Objects) (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ category text,
      pool.addresses firstBlock "logStatus" = some category ∧
      pool.addresses firstBlock message = some text ∧
      Stored signed heap category "logStatus" ∧ Stored signed heap text message ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (prog : Program E), prog.internal = program model m sigs →
         FailureContract sig tail (pool.addresses firstBlock) prog heap category text signed)

theorem prepared_correct (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (profile : Profile sig tail) (routed : Runtime.body model sig = CapabilityRejection.code)
    (fallthrough : constantFunction model m sig = Runtime.function model sig)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : sig ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++ (functions model m sigs).flatMap functionNames)}
    (made : prepare model m sigs = some pool) : PreparedContract model m sigs sig tail pool := by
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro prog actual inputs outputs arguments heap observed
    apply CapabilityRejection.null_call header objects (pool.addresses firstBlock) model profile routed arguments prog heap
    rw [actual]
    exact scalar_bound model m sigs unique sig member fallthrough
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, categoryBound⟩ := ConstantFunctions.text_bound model m sigs made Runtime.helpers[0]
      (List.mem_append_left _ (by simp [ConstantFunctions.helpers, TensorFunctions.helpers])) "logStatus" Logging.category_collected firstBlock
    obtain ⟨text, bound⟩ := ConstantFunctions.text_bound model m sigs made (Runtime.function model sig)
      (scalar_member model m sigs sig member fallthrough) message (CapabilityRejection.message_collected model routed) firstBlock
    have categoryStored := (pool.storage_valid before firstBlock signed "logStatus" category categoryBound).preserved frame
    have textStored := (pool.storage_valid before firstBlock signed message text bound).preserved frame
    refine ⟨category, text, categoryBound, bound, categoryStored, textStored, ?_⟩
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro E prog actual
    apply CapabilityRejection.failures_correct header objects (pool.addresses firstBlock) model profile routed prog heap category text signed
    · rw [actual]; exact scalar_bound model m sigs unique sig member fallthrough
    · rw [actual]; exact ConstantFunctions.helpers_bound model m sigs Runtime.helpers[0] (by simp [ConstantFunctions.helpers, TensorFunctions.helpers])
    · exact bound
    · exact categoryBound
    · exact categoryStored
    · exact textStored

structure FunctionContract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (sig : Signature) (tail : List Parameter) (text : String) : Prop where
  member : sig ∈ sigs
  profile : Profile sig tail
  printed : text = (Runtime.function model sig).render
  tokenization : Printer.FunctionTokenization RuntimePrinter.typedefs text (Runtime.function model sig)
  fragment : ∃ before after, ConstantFunctions.render model m sigs = before ++ text ++ after
  prepared : ∀ pool, prepare model m sigs = some pool → PreparedContract model m sigs sig tail pool

theorem rendered_contract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (profile : Profile sig tail) (routed : Runtime.body model sig = CapabilityRejection.code)
    (fallthrough : constantFunction model m sig = Runtime.function model sig)
    (printable : Printer.SignaturePrintable RuntimePrinter.typedefs sig)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : sig ∈ sigs) :
    FunctionContract model m sigs sig tail (Runtime.function model sig).render :=
  ⟨member, profile, rfl, RuntimePrinter.function_tokenization model sig printable,
    fallthrough ▸ ConstantFunctions.rendered_member model m sigs sig member,
    fun _ made => prepared_correct model m sigs profile routed fallthrough unique member made⟩

/-- The unsupported-capability family contract over the constant adapter list. -/
def FamilyContract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) : Prop :=
  ∀ sig ∈ CapabilityRejection.signatures,
    FunctionContract model m sigs sig sig.parameters.tail (Runtime.function model sig).render

theorem family_correct (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (members : ∀ sig ∈ CapabilityRejection.signatures, sig ∈ sigs) : FamilyContract model m sigs := by
  intro sig member
  exact rendered_contract model m sigs (CapabilityRejection.profiles sig member)
    (CapabilityRejection.routing model sig member) (capability_function model m sig member)
    (CapabilityRejection.signatures_printable sig member) unique (members sig member)

end ConstantCapabilityRejection

end Rumoca.FMI3
end
