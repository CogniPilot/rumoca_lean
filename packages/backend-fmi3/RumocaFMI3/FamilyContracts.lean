import RumocaFMI3.AbsentVariableContract
import RumocaFMI3.CapabilityRejectionFamily

/-! Profile-generic FMI 3 unsupported/absent-type function families.

Every FMI 3 adapter profile emits the same two function families over its
function list: the absent-type variable accessors and the unsupported-capability
rejections. Their execution bodies are identical to the scalar renderer's; a
profile differs only in the surrounding function list, its definition table and
its literal pool. `AdapterFamily` bundles exactly those per-profile pieces (the
per-signature dispatched function, the emitted list, the definition table, the
literal pool preparation, the render, and the definition-table/pool facts about
them), together with the profile's fallthrough routing of every family signature
to the scalar body. The two family contracts (`PreparedContract`,
`FunctionContract`, `FamilyContract`) and their correctness proofs are stated and
proved once over an `AdapterFamily`; each profile instantiates them with its own
`AdapterFamily` value, keeping every per-profile contract name and statement.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and neither the scalar renderer, the families nor any
existing contract changes. -/
noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory CLiteral.Interface

/-- The per-profile pieces the two function families are checked against: the
per-signature dispatched function (`pick`), the reused helper prefix (`helpers`),
the emitted function list (`functions`), the definition table (`program`), the
literal-pool preparation (`prepare`), the render (`render`), and the
definition-table and literal-pool facts about them, along with the profile's
fallthrough routing of every absent-type and unsupported-capability signature to
the scalar body. Every generic family contract below is stated over one of
these. -/
structure AdapterFamily (source : AST.Model) where
  /-- The compiled scalar witness model the emitted bodies are proved against. -/
  model : Solve.FMI3Model source
  /-- The dispatched emitted function for one pinned header signature. -/
  pick : Signature → Function
  /-- The reused helper prefix (the shared `fail` diagnostic first). -/
  helpers : List Function
  /-- The emitted function list: the helper prefix followed by one dispatched
  function per header signature, in header order. -/
  functions : List Signature → List Function
  /-- The emitted list is the helper prefix followed by the dispatched bodies. -/
  functions_def : ∀ sigs, functions sigs = helpers ++ sigs.map pick
  /-- The shared `fail` diagnostic is one of the helpers. -/
  fail_mem : Runtime.helpers[0] ∈ helpers
  /-- The definition table over the emitted list and the profile kernels. -/
  program : List Signature → CCalls.Program
  /-- The render of the emitted list. -/
  render : List Signature → String
  /-- Every listed header signature is bound to its dispatched body. -/
  function_bound : ∀ (sigs : List Signature),
    ((functions sigs).map (fun fn => fn.signature.name)).Nodup →
    ∀ (sig : Signature), sig ∈ sigs →
    (program sigs).definitions sig.name = some (.tree (pick sig))
  /-- Every helper is bound to its rendered tree. -/
  helpers_bound : ∀ (sigs : List Signature) (fn : Function), fn ∈ helpers →
    (program sigs).definitions fn.signature.name = some (.tree fn)
  /-- The literal pool preparation over the emitted list. -/
  prepare : (sigs : List Signature) →
    Option (Pool (LiteralPreparation.excluded ++ (functions sigs).flatMap functionNames))
  /-- Every collected occurrence has a constructed address. -/
  text_bound : ∀ (sigs : List Signature)
    {pool : Pool (LiteralPreparation.excluded ++ (functions sigs).flatMap functionNames)},
    prepare sigs = some pool → ∀ (fn : Function), fn ∈ functions sigs →
    ∀ (text : String), text ∈ functionTexts fn → ∀ (firstBlock : Nat),
    ∃ address, pool.addresses firstBlock text = some address
  /-- Each header signature is rendered exactly once at its actual list slot. -/
  rendered_member : ∀ (sigs : List Signature) (sig : Signature), sig ∈ sigs →
    ∃ before after : String, render sigs = before ++ (pick sig).render ++ after
  /-- Every absent-type family signature falls through the dispatch to the scalar
  body. -/
  absent_routes : ∀ (ty : AbsentVariables.VariableType) (write : Bool),
    pick (AbsentVariables.signature ty write) = Runtime.function model (AbsentVariables.signature ty write)
  /-- Every unsupported-capability signature falls through the dispatch to the
  scalar body. -/
  capability_routes : ∀ sig ∈ CapabilityRejection.signatures,
    pick sig = Runtime.function model sig

/-- The shared `fail` diagnostic is one of the emitted functions. -/
theorem AdapterFamily.fail_mem_functions {source : AST.Model} (fam : AdapterFamily source)
    (sigs : List Signature) : Runtime.helpers[0] ∈ fam.functions sigs := by
  rw [fam.functions_def]; exact List.mem_append_left _ fam.fail_mem

/-- Definition-table fact for any signature that renders the scalar body. -/
theorem AdapterFamily.scalarBound {source : AST.Model} (fam : AdapterFamily source)
    (sigs : List Signature)
    (unique : ((fam.functions sigs).map (fun fn => fn.signature.name)).Nodup)
    (sig : Signature) (member : sig ∈ sigs)
    (routed : fam.pick sig = Runtime.function fam.model sig) :
    (fam.program sigs).definitions sig.name = some (.tree (Runtime.function fam.model sig)) := by
  rw [← routed]; exact fam.function_bound sigs unique sig member

/-- List membership of a scalar body rendered by the profile list. -/
theorem AdapterFamily.scalarMember {source : AST.Model} (fam : AdapterFamily source)
    (sigs : List Signature) (sig : Signature) (member : sig ∈ sigs)
    (routed : fam.pick sig = Runtime.function fam.model sig) :
    Runtime.function fam.model sig ∈ fam.functions sigs := by
  rw [← routed, fam.functions_def]; exact List.mem_append_right _ (List.mem_map.mpr ⟨sig, member, rfl⟩)

/-! ### Absent-type variable family -/

namespace AbsentFamily
open AbsentVariables

variable {source : AST.Model}

/-- The absent-type prepared contract over a profile's definition table and
literal pool. Same shape as the scalar `AbsentVariables.PreparedContract`, but the
function table is the profile list's. -/
structure PreparedContract (fam : AdapterFamily source)
    (sigs : List Signature) (ty : VariableType) (write : Bool)
    (pool : Pool (LiteralPreparation.excluded ++ (fam.functions sigs).flatMap functionNames)) : Prop where
  quiet : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (prog : Program E),
      prog.internal = fam.program sigs → QuietContract ty write prog
  staticQuiet : ∀ (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := executionInterface objects (pool.addresses firstBlock)
    ∀ (prog : Program E),
      prog.internal = fam.program sigs → QuietContract ty write prog
  failures : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool)
    (objects : Objects) (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ (category : Address) (messages : Failure → Address),
      pool.addresses firstBlock "logStatus" = some category ∧
      (∀ reason, pool.addresses firstBlock (failureMessage reason) = some (messages reason)) ∧
      Stored signed heap category "logStatus" ∧ (∀ reason, Stored signed heap (messages reason) (failureMessage reason)) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (prog : Program E),
         prog.internal = fam.program sigs → ∀ reason, SuppressedContract ty write reason prog heap) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (prog : Program Invocation),
         prog.internal = fam.program sigs →
         ∀ reason, LoggedContract ty write reason prog category (messages reason) heap signed)

theorem prepared_correct (fam : AdapterFamily source)
    (sigs : List Signature) (ty : VariableType) (write : Bool)
    (unique : ((fam.functions sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ty write ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++ (fam.functions sigs).flatMap functionNames)}
    (made : fam.prepare sigs = some pool) : PreparedContract fam sigs ty write pool := by
  have routed := fam.absent_routes ty write
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro prog actual
    apply AbsentVariables.quiet_correct header objects (pool.addresses firstBlock) fam.model ty write prog
    rw [actual]
    exact fam.scalarBound sigs unique (signature ty write) member routed
  · intro E objects firstBlock
    letI : CInterface := executionInterface objects (pool.addresses firstBlock)
    intro prog actual
    apply AbsentVariables.quiet_static_correct objects (pool.addresses firstBlock) fam.model ty write prog
    rw [actual]
    exact fam.scalarBound sigs unique (signature ty write) member routed
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, categoryBound⟩ := fam.text_bound sigs made Runtime.helpers[0]
      (fam.fail_mem_functions sigs) "logStatus" Logging.category_collected firstBlock
    have available : ∀ reason, ∃ message, pool.addresses firstBlock (failureMessage reason) = some message := by
      intro reason
      exact fam.text_bound sigs made (Runtime.function fam.model (signature ty write))
        (fam.scalarMember sigs (signature ty write) member routed)
        (failureMessage reason) (AbsentVariables.message_collected fam.model ty write reason) firstBlock
    choose messages messageBound using available
    have categoryStored := (pool.storage_valid before firstBlock signed "logStatus" category categoryBound).preserved frame
    have messageStored : ∀ reason, Stored signed heap (messages reason) (failureMessage reason) := fun reason =>
      (pool.storage_valid before firstBlock signed (failureMessage reason) (messages reason) (messageBound reason)).preserved frame
    let literals := pool.addresses firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    have definitions : ∀ (E : Type) (prog : Program E),
        prog.internal = fam.program sigs →
        prog.internal.definitions (signature ty write).name =
          some (.tree (Runtime.function fam.model (signature ty write))) ∧
        prog.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
      intro E prog actual
      refine ⟨?_, ?_⟩
      · rw [actual]; exact fam.scalarBound sigs unique (signature ty write) member routed
      · rw [actual]; exact fam.helpers_bound sigs Runtime.helpers[0] fam.fail_mem
    refine ⟨category, messages, categoryBound, messageBound, categoryStored, messageStored, ?_, ?_⟩
    · intro E prog actual reason
      obtain ⟨defined, helper⟩ := definitions E prog actual
      exact AbsentVariables.suppressed_correct header objects literals fam.model ty write reason prog
        (messages reason) heap defined helper (messageBound reason)
    · intro prog actual reason
      obtain ⟨defined, helper⟩ := definitions Invocation prog actual
      exact AbsentVariables.logged_correct header objects literals fam.model ty write reason prog category
        (messages reason) heap signed defined helper categoryBound (messageBound reason) categoryStored (messageStored reason)

structure FunctionContract (fam : AdapterFamily source)
    (sigs : List Signature) (ty : VariableType) (write : Bool) (text : String) : Prop where
  member : signature ty write ∈ sigs
  printed : text = (Runtime.function fam.model (signature ty write)).render
  tokenization : Printer.FunctionTokenization RuntimePrinter.typedefs text (Runtime.function fam.model (signature ty write))
  prepared : ∀ pool, fam.prepare sigs = some pool → PreparedContract fam sigs ty write pool

theorem rendered_contract (fam : AdapterFamily source)
    (sigs : List Signature) (ty : VariableType) (write : Bool)
    (unique : ((fam.functions sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ty write ∈ sigs) :
    FunctionContract fam sigs ty write (Runtime.function fam.model (signature ty write)).render :=
  ⟨member, rfl,
    RuntimePrinter.function_tokenization fam.model (signature ty write) (AbsentVariables.signature_printable ty write),
    fun _ made => prepared_correct fam sigs ty write unique member made⟩

/-- The absent-type family contract over a profile's list. -/
def FamilyContract (fam : AdapterFamily source) (sigs : List Signature) : Prop :=
  ∀ ty write, FunctionContract fam sigs ty write (Runtime.function fam.model (signature ty write)).render

theorem family_correct (fam : AdapterFamily source) (sigs : List Signature)
    (unique : ((fam.functions sigs).map (fun fn => fn.signature.name)).Nodup)
    (members : ∀ ty write, signature ty write ∈ sigs) : FamilyContract fam sigs :=
  fun ty write => rendered_contract fam sigs ty write unique (members ty write)

end AbsentFamily

/-! ### Unsupported-capability family -/

namespace CapabilityFamily
open CapabilityRejection

variable {source : AST.Model}

structure PreparedContract (fam : AdapterFamily source)
    (sigs : List Signature) (sig : Signature) (tail : List Parameter)
    (pool : Pool (LiteralPreparation.excluded ++ (fam.functions sigs).flatMap functionNames)) : Prop where
  null : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (prog : Program E), prog.internal = fam.program sigs →
      NullContract sig tail (pool.addresses firstBlock) prog
  failures : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool)
    (objects : Objects) (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ category text,
      pool.addresses firstBlock "logStatus" = some category ∧
      pool.addresses firstBlock message = some text ∧
      Stored signed heap category "logStatus" ∧ Stored signed heap text message ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (prog : Program E), prog.internal = fam.program sigs →
         FailureContract sig tail (pool.addresses firstBlock) prog heap category text signed)

theorem prepared_correct (fam : AdapterFamily source)
    (sigs : List Signature) {sig : Signature} {tail : List Parameter}
    (profile : Profile sig tail) (routed : Runtime.body fam.model sig = CapabilityRejection.code)
    (fallthrough : fam.pick sig = Runtime.function fam.model sig)
    (unique : ((fam.functions sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : sig ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++ (fam.functions sigs).flatMap functionNames)}
    (made : fam.prepare sigs = some pool) : PreparedContract fam sigs sig tail pool := by
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro prog actual inputs outputs arguments heap observed
    apply CapabilityRejection.null_call header objects (pool.addresses firstBlock) fam.model profile routed arguments prog heap
    rw [actual]
    exact fam.scalarBound sigs unique sig member fallthrough
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, categoryBound⟩ := fam.text_bound sigs made Runtime.helpers[0]
      (fam.fail_mem_functions sigs) "logStatus" Logging.category_collected firstBlock
    obtain ⟨text, bound⟩ := fam.text_bound sigs made (Runtime.function fam.model sig)
      (fam.scalarMember sigs sig member fallthrough) message (CapabilityRejection.message_collected fam.model routed) firstBlock
    have categoryStored := (pool.storage_valid before firstBlock signed "logStatus" category categoryBound).preserved frame
    have textStored := (pool.storage_valid before firstBlock signed message text bound).preserved frame
    refine ⟨category, text, categoryBound, bound, categoryStored, textStored, ?_⟩
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro E prog actual
    apply CapabilityRejection.failures_correct header objects (pool.addresses firstBlock) fam.model profile routed prog heap category text signed
    · rw [actual]; exact fam.scalarBound sigs unique sig member fallthrough
    · rw [actual]; exact fam.helpers_bound sigs Runtime.helpers[0] fam.fail_mem
    · exact bound
    · exact categoryBound
    · exact categoryStored
    · exact textStored

structure FunctionContract (fam : AdapterFamily source)
    (sigs : List Signature) (sig : Signature) (tail : List Parameter) (text : String) : Prop where
  member : sig ∈ sigs
  profile : Profile sig tail
  printed : text = (Runtime.function fam.model sig).render
  tokenization : Printer.FunctionTokenization RuntimePrinter.typedefs text (Runtime.function fam.model sig)
  fragment : ∃ before after, fam.render sigs = before ++ text ++ after
  prepared : ∀ pool, fam.prepare sigs = some pool → PreparedContract fam sigs sig tail pool

theorem rendered_contract (fam : AdapterFamily source)
    (sigs : List Signature) {sig : Signature} {tail : List Parameter}
    (profile : Profile sig tail) (routed : Runtime.body fam.model sig = CapabilityRejection.code)
    (fallthrough : fam.pick sig = Runtime.function fam.model sig)
    (printable : Printer.SignaturePrintable RuntimePrinter.typedefs sig)
    (unique : ((fam.functions sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : sig ∈ sigs) :
    FunctionContract fam sigs sig tail (Runtime.function fam.model sig).render :=
  ⟨member, profile, rfl, RuntimePrinter.function_tokenization fam.model sig printable,
    fallthrough ▸ fam.rendered_member sigs sig member,
    fun _ made => prepared_correct fam sigs profile routed fallthrough unique member made⟩

/-- The unsupported-capability family contract over a profile's list. -/
def FamilyContract (fam : AdapterFamily source) (sigs : List Signature) : Prop :=
  ∀ sig ∈ CapabilityRejection.signatures,
    FunctionContract fam sigs sig sig.parameters.tail (Runtime.function fam.model sig).render

theorem family_correct (fam : AdapterFamily source) (sigs : List Signature)
    (unique : ((fam.functions sigs).map (fun fn => fn.signature.name)).Nodup)
    (members : ∀ sig ∈ CapabilityRejection.signatures, sig ∈ sigs) : FamilyContract fam sigs := by
  intro sig member
  exact rendered_contract fam sigs (CapabilityRejection.profiles sig member)
    (CapabilityRejection.routing fam.model sig member) (fam.capability_routes sig member)
    (CapabilityRejection.signatures_printable sig member) unique (members sig member)

end CapabilityFamily

end Rumoca.FMI3
end
