import RumocaFMI3.FactoryLiterals
import RumocaFMI3.RuntimePrinter

/-! Admission and rejection contracts for the two actual public factories.
Creation after successful admission remains a separate obligation. The
contract combines public-call prefixes with complete rejection fragments,
using one definition table, prepared literal pool and host-call semantics. -/
noncomputable section
namespace Rumoca.FMI3.FactoryAdmission
open CTree CMemory CBody CLiteral CStringMemory FactoryArguments FactoryLiterals
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

structure ExecutionContract (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (addresses : Field → Address) : Prop where
  valid : Identity.Bindings program → ∀ (kind : Kind) (args : Raw)
    (name suppliedToken : Address) (nameBytes tokenBytes : List UInt8),
    (kind = .me ∨ FactoryEntry.unsupported args = false) →
    args.name = some name → args.token = some suppliedToken →
    Contents heap name nameBytes → Contents heap suppliedToken tokenBytes → nameBytes.length < 2^64 →
    ∀ stack, ∃ types, ∀ behavior,
      (CCalls.Events.machine program).Behaves (.calling (signature kind).name (arguments kind args) heap stack) behavior ↔
      (CCalls.Events.machine program).Behaves
        (.body (.running (FactoryValidation.remaining model kind
          (Identity.accepted nameBytes (content (text model .whitespace)) tokenBytes (content (token model))))
          (FactoryValidation.locals kind args
            (Identity.accepted nameBytes (content (text model .whitespace)) tokenBytes (content (token model))))
          types heap) "fmi3Instance" stack) behavior
  missing : ∀ (kind : Kind) (args : Raw),
    (kind = .me ∨ FactoryEntry.unsupported args = false) →
    (args.name.isNone || args.token.isNone) = true → ∀ stack, ∃ types, ∀ behavior,
      (CCalls.Events.machine program).Behaves (.calling (signature kind).name (arguments kind args) heap stack) behavior ↔
      (CCalls.Events.machine program).Behaves
        (.body (.running (FactoryRejection.code (text model .identity) ++ (Runtime.makeInstance model kind).drop 2)
          (FactoryNull.rejected kind args) types heap) "fmi3Instance" stack) behavior
  unsupported : ∀ args : Raw, FactoryEntry.unsupported args = true → ∀ stack, ∃ types,
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling (signature .cs).name (arguments .cs args) heap stack)
      (.body (.running (FactoryRejection.code (text model .capability) ++ Runtime.makeInstance model .cs)
        (parameters .cs args) types heap) "fmi3Instance" stack)
  quiet : ∀ (field : Field) (env : Locals) (types : CLoops.Types) (rest : List Stmt)
    (logger : Option Address) (logging : Bool),
    resolve env "logMessage" = some (.pointer logger) →
    resolve env "loggingOn" = some (boolean logging) → resolve env "NULL" = some (.pointer none) →
    (logger.isSome && logging) = false → ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.body (.running (FactoryRejection.code (text model field) ++ rest) env types heap) "fmi3Instance" .done) behavior ↔
      behavior = .terminates [] ⟨.pointer none, heap⟩
  logged : ∀ (field : Field) (env : Locals) (types : CLoops.Types) (rest : List Stmt)
    (logger : Address) (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    env "logMessage" = some (.pointer (some logger)) →
    resolve env "loggingOn" = some (boolean true) →
    resolve env "instanceEnvironment" = some (.pointer environment) →
    resolve env "fmi3Error" = some (.integer 3) → resolve env "NULL" = some (.pointer none) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name → ∀ behavior,
      ((CCalls.Events.machine program).Behaves
        (.body (.running (FactoryRejection.code (text model field) ++ rest) env types heap) "fmi3Instance" .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment (addresses .category) (addresses field))
          heap events value after ∧ behavior = .terminates events ⟨.pointer none, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment (addresses .category) (addresses field))
          heap events value after) ∧ behavior = .wrong [])) ∧
      (∀ events value after, foreign.execute (Logging.arguments environment (addresses .category) (addresses field))
        heap events value after → ∀ item,
        Contents after (addresses item) (content (text model item)))

theorem execution_correct (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (addresses : Field → Address) (signed : Bool)
    (definitions : ∀ kind, program.internal.definitions (signature kind).name =
      some (.tree (Runtime.function model (signature kind))))
    (helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function))
    (bound : ∀ field, static.addresses (text model field) = some (addresses field))
    (stored : ∀ field, Stored signed heap (addresses field) (text model field)) :
    ExecutionContract model program heap addresses := by
  constructor
  · intro bindings kind args name suppliedToken nameBytes tokenBytes supported nameBound tokenBound
      nameStored tokenStored fits stack
    exact FactoryValidation.admission_equivalence program bindings model kind args heap stack
      name suppliedToken (addresses .expected) (addresses .whitespace) nameBytes tokenBytes
      (content (token model)) (content (text model .whitespace)) (definitions kind) helper supported
      nameBound tokenBound (bound .expected) (bound .whitespace)
      nameStored tokenStored (literal_contents (stored .expected)) (literal_contents (stored .whitespace)) fits
  · intro kind args supported missing stack
    exact FactoryNull.reaches_rejection program model kind args heap stack (addresses .expected) (addresses .whitespace)
      (definitions kind) helper supported missing (bound .expected) (bound .whitespace)
  · intro args unsupported stack
    exact FactoryUnsupported.rejection_entry program model args heap stack (definitions .cs) unsupported
  · intro field env types rest logger logging loggerBound loggingBound nullBound quiet behavior
    rw [FactoryRejection.silent_equivalence program (text model field) env types heap rest .done
      logger logging loggerBound loggingBound nullBound quiet behavior]
    exact (CCalls.Events.return_forced program (.pointer none) heap).behaviors behavior
  · intro field env types rest logger environment name foreign loggerBound loggingBound
      environmentBound errorBound nullBound address external prototype behavior
    refine ⟨FactoryRejection.all_behaviors program (text model field) env types heap rest
      logger (addresses .category) (addresses field) environment name foreign loggerBound loggingBound
      environmentBound errorBound nullBound (bound .category) (bound field) address external prototype behavior, ?_⟩
    intro events value after executed item
    exact (FactoryLiterals.preserved model addresses heap after signed stored
      (foreign.readonly _ _ _ _ _ executed) item).2

end Rumoca.FMI3.FactoryAdmission

noncomputable section
namespace Rumoca.FMI3.FactoryAdmission
open CTree CMemory CLiteral FactoryArguments FactoryLiterals

def PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop :=
  ∀ (before : Heap) (firstBlock : Nat) (signed : Bool), ∃ addresses : Field → Address,
    (∀ field, pool.addresses firstBlock (text model field) = some (addresses field) ∧
      Stored signed (pool.install before firstBlock signed) (addresses field) (text model field)) ∧
    ∀ (E : Type) (program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) E),
      @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program =
        LiteralPreparation.program model sigs →
      ExecutionContract (static := ⟨pool.addresses firstBlock⟩) model program
        (pool.install before firstBlock signed) addresses

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : ∀ kind, signature kind ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  intro before firstBlock signed
  obtain ⟨addresses, strings⟩ := FactoryLiterals.prepared model sigs (member .cs) made before firstBlock signed
  refine ⟨addresses, fun field => ⟨(strings field).1, (strings field).2.1⟩, ?_⟩
  intro E program same
  have definitions : ∀ kind,
      (@CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program).definitions
        (signature kind).name = some (.tree (Runtime.function model (signature kind))) := by
    intro kind
    rw [same]
    exact LiteralPreparation.function_bound model sigs unique (signature kind) (member kind)
  have helper : (@CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program).definitions
      Identity.function.signature.name = some (.tree Identity.function) := by
    rw [same]
    exact Identity.helper_defined model sigs
  exact execution_correct (static := ⟨pool.addresses firstBlock⟩) model program
    (pool.install before firstBlock signed) addresses signed definitions helper
    (fun field => (strings field).1) (fun field => (strings field).2.1)

/-- Each public function's exact text, independent tokenization and location
share the prepared execution contract. This is an admission/rejection contract,
not a claim that the successful creation suffix is already verified. -/
structure FunctionContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (texts : Kind → String) : Prop where
  member : ∀ kind, signature kind ∈ sigs
  printed : ∀ kind, texts kind = (Runtime.function model (signature kind)).render
  tokenization : ∀ kind, Printer.FunctionTokenization RuntimePrinter.typedefs
    (texts kind) (Runtime.function model (signature kind))
  located : ∀ kind, ∃ before after, Runtime.render model sigs = before ++ texts kind ++ after
  prepared : ∀ pool, LiteralPreparation.prepare model sigs = some pool → PreparedContract model sigs pool

theorem rendered_contract (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : ∀ kind, signature kind ∈ sigs)
    (printable : ∀ kind, Printer.SignaturePrintable RuntimePrinter.typedefs (signature kind)) :
    FunctionContract model sigs (fun kind => (Runtime.function model (signature kind)).render) := by
  refine ⟨member, fun _ => rfl, ?_, ?_, fun _ made => prepared_correct model sigs unique member made⟩
  · intro kind
    exact RuntimePrinter.function_tokenization model (signature kind) (printable kind)
  · intro kind
    exact LiteralPreparation.rendered_member model sigs (signature kind) (member kind)

end Rumoca.FMI3.FactoryAdmission
