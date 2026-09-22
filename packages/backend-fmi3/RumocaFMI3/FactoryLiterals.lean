import RumocaFMI3.FactoryUnsupported
import RumocaFMI3.FactoryNull
import RumocaFMI3.FactoryValidation

/-! Construct all factory-admission string objects from the same function
collection used by the renderer. Their readonly storage survives every
represented callback outcome. Native declarations/layout remain separate. -/
noncomputable section
namespace Rumoca.FMI3.FactoryLiterals
open CTree CMemory CLiteral CStringMemory FactoryArguments

inductive Field where
  | expected | whitespace | category | identity | capability
  deriving DecidableEq

def text (model : Solve.FMI3Model source) : Field → String
  | .expected => token model
  | .whitespace => " \t\n\r\u000c\u000b"
  | .category => "logStatus"
  | .identity => "Invalid name or instantiation token"
  | .capability => FactoryUnsupported.message

/-- CS carries both identity and capability diagnostics, so a single actual
function supplies the common ME/CS admission pool. -/
theorem collected (model : Solve.FMI3Model source) (field : Field) :
    text model field ∈ functionTexts (Runtime.function model (signature .cs)) := by
  cases field <;>
    simp [text, Runtime.function, Runtime.body, signature, Identity.factoryName,
      Runtime.makeInstance, FactoryUnsupported.message,
      FactoryPrefix.validation, FactoryPrefix.identityGuard, FactoryPrefix.capabilityGuard,
      FactoryRejection.code, FactoryRejection.logCall,
      functionTexts, statementTexts, expressionTexts]

theorem prepared (model : Solve.FMI3Model source) (sigs : List Signature)
    (member : signature .cs ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) :
    ∃ addresses : Field → Address, ∀ field,
      pool.addresses firstBlock (text model field) = some (addresses field) ∧
      Stored signed (pool.install before firstBlock signed) (addresses field) (text model field) ∧
      Contents (pool.install before firstBlock signed) (addresses field) (content (text model field)) := by
  have each : ∀ field, ∃ address, pool.addresses firstBlock (text model field) = some address := by
    intro field
    exact LiteralPreparation.message_bound model sigs made (signature .cs) member
      (text model field) (collected model field) firstBlock
  choose addresses bound using each
  refine ⟨addresses, fun field => ?_⟩
  have stored := pool.storage_valid before firstBlock signed _ _ (bound field)
  exact ⟨bound field, stored, literal_contents stored⟩

/-- The native host's represented write effects cannot corrupt prepared
diagnostic text. Private writable instance fields need a stronger frame. -/
theorem preserved (model : Solve.FMI3Model source) (addresses : Field → Address)
    (before after : Heap) (signed : Bool)
    (stored : ∀ field, Stored signed before (addresses field) (text model field))
    (frame : CReadOnly.Preserves before after) :
    ∀ field, Stored signed after (addresses field) (text model field) ∧
      Contents after (addresses field) (content (text model field)) := by
  intro field
  have kept := (stored field).preserved frame
  exact ⟨kept, literal_contents kept⟩

end Rumoca.FMI3.FactoryLiterals
