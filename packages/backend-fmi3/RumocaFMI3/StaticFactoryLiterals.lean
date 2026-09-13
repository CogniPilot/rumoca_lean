import RumocaFMI3.StaticRuntimeLinkage
import RumocaC.StringLiteralContents

/-! Construct the storage-exhaustion diagnostic from the actual runtime's
literal pool and preserve its bytes across represented readonly frames. -/
noncomputable section
namespace Rumoca.FMI3.StaticFactory
open CTree CMemory CLiteral CStringMemory

/-- Exhaustion text is collected from the actual public factory, rather than
inserted into an assumed literal environment by the execution theorem. -/
theorem capacity_message_collected (model : Solve.FMI3Model source) :
    "Instance capacity exhausted" ∈ functionTexts
      (Runtime.function model (FactoryArguments.signature .cs)) := by
  rw [StaticRuntime.factory_definition]
  simp [StaticFactory.function, FactoryPrefix.body, FactoryPrefix.entry, StaticFactory.code, StaticFactory.guard,
    StaticFactory.exhausted, FactoryRejection.code, FactoryRejection.logCall,
    functionTexts, statementTexts, expressionTexts]

theorem capacity_message_prepared (model : Solve.FMI3Model source) (signatures : List Signature)
    (member : FactoryArguments.signature .cs ∈ signatures)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model signatures).flatMap functionNames)}
    (made : LiteralPreparation.prepare model signatures = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap) :
    ∃ address, pool.addresses firstBlock "Instance capacity exhausted" = some address ∧
      Stored signed heap address "Instance capacity exhausted" ∧
      Contents heap address (content "Instance capacity exhausted") := by
  obtain ⟨address, bound⟩ := LiteralPreparation.message_bound model signatures made
    (FactoryArguments.signature .cs) member "Instance capacity exhausted"
    (capacity_message_collected model) firstBlock
  have kept := (pool.storage_valid before firstBlock signed _ _ bound).preserved frame
  exact ⟨address, bound, kept, literal_contents kept⟩

end Rumoca.FMI3.StaticFactory
