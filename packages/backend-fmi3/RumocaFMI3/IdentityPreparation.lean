import RumocaFMI3.IdentityContract
import RumocaFMI3.FactoryPrefixCode
import RumocaC.StringLiteralContents

/-! Construct the validator's constant buffers from the literal pool collected
from the actual creation function. Caller strings still need valid readable
storage. Native translation-unit storage and complete creation remain separate. -/
noncomputable section
namespace Rumoca.FMI3.Identity
open CTree CMemory CLiteral CStringMemory

theorem constants_collected (model : Solve.FMI3Model source) (sig : Signature) (kind : Kind)
    (named : sig.name = factoryName kind) :
    token model ∈ functionTexts (Runtime.function model sig) ∧
      " \t\n\r\u000c\u000b" ∈ functionTexts (Runtime.function model sig) := by
  cases kind <;> simp only [factoryName] at named
  all_goals simp [Runtime.function, Runtime.body, named, Runtime.makeInstance,
    FactoryPrefix.validation, FactoryPrefix.identityGuard, FactoryPrefix.capabilityGuard,
    FactoryRejection.code, FactoryRejection.logCall,
    functionTexts, statementTexts, expressionTexts, Runtime.call, Runtime.v]

theorem constants_ready (model : Solve.FMI3Model source) (sigs : List Signature)
    (sig : Signature) (member : sig ∈ sigs) (kind : Kind) (named : sig.name = factoryName kind)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) :
    ∃ expected whitespace : Address,
      pool.addresses firstBlock (token model) = some expected ∧
      pool.addresses firstBlock " \t\n\r\u000c\u000b" = some whitespace ∧
      Contents (pool.install before firstBlock signed) expected (content (token model)) ∧
      Contents (pool.install before firstBlock signed) whitespace (content " \t\n\r\u000c\u000b") := by
  obtain ⟨expectedCollected, whitespaceCollected⟩ := constants_collected model sig kind named
  obtain ⟨expected, expectedBound⟩ := LiteralPreparation.message_bound model sigs made sig member
    (token model) expectedCollected firstBlock
  obtain ⟨whitespace, whitespaceBound⟩ := LiteralPreparation.message_bound model sigs made sig member
    " \t\n\r\u000c\u000b" whitespaceCollected firstBlock
  exact ⟨expected, whitespace, expectedBound, whitespaceBound,
    literal_contents (pool.storage_valid before firstBlock signed _ _ expectedBound),
    literal_contents (pool.storage_valid before firstBlock signed _ _ whitespaceBound)⟩

/-- Expected-token/whitespace addresses and their contents are constructed,
not extra successful-lookup premises. Execution uses the definition table of
the same function collection. Every later caller observation is retained. -/
theorem prepared_equivalence (model : Solve.FMI3Model source) (sigs : List Signature)
    (sig : Signature) (member : sig ∈ sigs) (kind : Kind) (named : sig.name = factoryName kind)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) :
    ∃ expected whitespace : Address,
      pool.addresses firstBlock (token model) = some expected ∧
      pool.addresses firstBlock " \t\n\r\u000c\u000b" = some whitespace ∧
      ∀ (E : Type) (program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) E),
        @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program =
          LiteralPreparation.program model sigs →
        Bindings (interface := cInterface (pool.addresses firstBlock)) program →
        ∀ (name suppliedToken : Address) (nameBytes tokenBytes : List UInt8),
          Contents (pool.install before firstBlock signed) name nameBytes →
          Contents (pool.install before firstBlock signed) suppliedToken tokenBytes →
          nameBytes.length < 2^64 →
          ∀ (stack : CCalls.Typed.Continuation) (behavior : Transition.Events.Observation E CBody.Result),
            (@CCalls.Events.machine E (cInterface (pool.addresses firstBlock)) program).Behaves
              (.calling function.signature.name
                (Arguments.values ⟨some name, some suppliedToken, some expected, some whitespace⟩)
                (pool.install before firstBlock signed) stack) behavior ↔
            (@CCalls.Events.machine E (cInterface (pool.addresses firstBlock)) program).Behaves
              (.returning (CBody.boolean
                (accepted nameBytes (content " \t\n\r\u000c\u000b") tokenBytes (content (token model))))
                (pool.install before firstBlock signed) stack) behavior := by
  letI : CInterface := cInterface (pool.addresses firstBlock)
  obtain ⟨expected, whitespace, expectedBound, whitespaceBound, expectedStored, whitespaceStored⟩ :=
    constants_ready model sigs sig member kind named made before firstBlock signed
  refine ⟨expected, whitespace, expectedBound, whitespaceBound, ?_⟩
  intro E program same bindings name suppliedToken nameBytes tokenBytes nameStored tokenStored fits stack behavior
  exact (execution_correct (interface := cInterface (pool.addresses firstBlock)) model sigs program same).valid
    bindings name suppliedToken expected whitespace nameBytes tokenBytes (content (token model))
    (content " \t\n\r\u000c\u000b") (pool.install before firstBlock signed)
    nameStored tokenStored expectedStored whitespaceStored fits stack behavior

end Rumoca.FMI3.Identity
