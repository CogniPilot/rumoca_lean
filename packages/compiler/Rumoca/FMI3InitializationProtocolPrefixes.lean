import Rumoca.FMI3InitializationProtocol
import RumocaFMI3.InitializationProtocolInterrupted

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CMemory StaticFactory CCalls.Events

/-- Every completed initialization observation and source checkpoint remains
available when the next call blocks. Admission of that call is not its return. -/
structure SourcePrefix (model : Solve.FMI3Model source) (p : Address)
    (kind : Kind) (before : State) (actions : List Action) (stop : StopRecord) : Prop where
  script : actions = stop.done ++ stop.pending :: stop.rest
  observations : Observed model before stop.done stop.observed
  checkpoints : List.Forall₂ (SourceCheckpoint source p) (exitStates before stop.done) stop.checkpoints
  admitted : ∃ state, ReferenceTrace kind before stop.done state ∧ stop.pending.Allowed kind state

/-- Both FMI interfaces reuse the universal initialization compiler on the
actual completed prefix; no execution of the pending suffix is required. -/
theorem SourcePrefix.of_compiler [CInterface] {source : AST.Model} {model : Solve.FMI3Model source}
    {program : Program Invocation} {objects : Objects} {owners : SlotOwners.State objects.capacity}
    (compiler : ∀ heap actions state,
      Invariant program objects retained owners original literals heap p kind before →
      ReferenceTrace kind before actions state →
      (∀ action ∈ actions, action.Prepared objects retained original p access) →
      SourceContract model program objects retained owners original literals heap p access kind before state actions)
    (invariant : Invariant program objects retained owners original literals heap p kind before)
    (reference : ReferenceTrace kind before actions final)
    (prepared : ∀ action ∈ actions, action.Prepared objects retained original p access)
    (actual : Interrupted program p access heap actions stop) :
    SourcePrefix model p kind before actions stop := by
  have split := reference
  rw [actual.1] at split
  obtain ⟨middle, prefixTrace, suffixTrace⟩ := split.split
  have requests : ∀ action ∈ stop.done, action.Prepared objects retained original p access := by
    intro action member
    apply prepared action
    rw [actual.1]
    exact List.mem_append_left _ member
  have certified := compiler heap stop.done middle invariant prefixTrace requests
  obtain ⟨observations, checkpoints, _, _, _, _⟩ := certified.completed _ _ _ actual.2.1
  cases suffixTrace with
  | cons allowed _ => exact ⟨actual.1, observations, checkpoints, middle, prefixTrace, allowed⟩

end Rumoca.FMI3.InitializationProtocol
end
