import RumocaFMI3.DebugLoggingRuntime

/-! The public contract is instantiated from the actual table and immutable
pool. It applies after preceding calls preserve that pool; it neither assumes
an error-helper result nor a returning logging callback. -/
noncomputable section
namespace Rumoca.FMI3.DebugLogging
open CTree CMemory StaticFactory CLiteral CStringMemory

structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  null : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model sigs →
      ∀ heap enabled count pointer behavior,
        (CCalls.Events.machine program).Behaves
          (.calling signature.name (arguments none enabled count pointer) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 3, heap⟩
  execution : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool)
    (objects : Objects) (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ (category : Address) (messages : Bool → Address),
      pool.addresses firstBlock "logStatus" = some category ∧
      (∀ unknown, pool.addresses firstBlock (failureMessage unknown) = some (messages unknown)) ∧
      Contents heap category (content "logStatus") ∧
      (∀ unknown, Stored signed heap (messages unknown) (failureMessage unknown)) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : CCalls.Events.Program E),
         program.internal = LiteralPreparation.program model sigs →
         program.externals "strcmp" = some (CStringCalls.compareExternal (by rfl)) →
         SuppressedContract program heap ∧ LoggedContract program heap category messages)

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ∈ sigs) (emitted : Runtime.function model signature = function)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro program actual
    have definitions := prepared_definitions model sigs unique member emitted header objects
      (pool.addresses firstBlock) program actual
    exact runtime_null_correct header objects (pool.addresses firstBlock) program definitions.1
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, messages, literal, bound, contents, stored⟩ :=
      prepared_literals model sigs member emitted made before firstBlock signed heap frame
    refine ⟨category, messages, literal, bound, contents, stored, ?_⟩
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro E program actual compare
    obtain ⟨defined, helper⟩ := prepared_definitions model sigs unique member emitted header objects
      (pool.addresses firstBlock) program actual
    exact ⟨runtime_suppressed_correct header objects (pool.addresses firstBlock) program heap category messages
      defined helper compare literal bound contents,
      runtime_logged_correct header objects (pool.addresses firstBlock) program heap category messages
        defined helper compare literal bound contents⟩

end Rumoca.FMI3.DebugLogging
end
