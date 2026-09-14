import RumocaFMI3.CSRunInterrupted
import RumocaFMI3.InitializationProtocolInterrupted
import RumocaFMI3.InitializationSimulation
import Rumoca.FMI3CSRunRecords

noncomputable section
namespace Rumoca.FMI3
open CMemory StaticFactory CCalls.Events

/-- Every completed initialization observation and source checkpoint remains
available when the next call blocks. Admission of that call is not its return. -/
structure InitializationProtocol.SourcePrefix (model : Solve.FMI3Model source) (p : Address)
    (kind : Kind) (before : InitializationProtocol.State) (actions : List InitializationProtocol.Action)
    (stop : InitializationProtocol.StopRecord) : Prop where
  script : actions = stop.done ++ stop.pending :: stop.rest
  observations : InitializationProtocol.Observed model before stop.done stop.observed
  checkpoints : List.Forall₂ (InitializationProtocol.SourceCheckpoint source p)
    (InitializationProtocol.exitStates before stop.done) stop.checkpoints
  admitted : ∃ state, InitializationProtocol.ReferenceTrace kind before stop.done state ∧ stop.pending.Allowed kind state

def CSRun.SourcePrefix (source : AST.Model) (header : CFenv.Header) (p : Address) (buffers : StepEntry.Buffers)
    (heap : Heap) (before : CSRun.Reference) (actions : List CSRun.Action) (stop : CSRun.StopRecord Invocation) : Prop :=
  actions = stop.done ++ stop.pending :: stop.rest ∧
  ∃ reference, CSRun.SourceTrace source header p buffers heap before stop.done stop.statuses stop.calls stop.heap reference ∧
    CSRun.SourceSample source p reference stop.heap ∧
    (∃ next status, CSRun.Change header p buffers reference stop.pending next status) ∧
    ∃ request outputs, stop.pending = .step request outputs

namespace CSProtocol
open InitializationProtocol (Invariant Persistent CSExecution SourceContract)

def InitializationCompiler [CInterface] (model : Solve.FMI3Model source) (program : Program Invocation) (objects : Objects)
    (retained : Address → Prop) (owners : SlotOwners.State objects.capacity) (original literals : Heap)
    (p : Address) (access : Float64Buffers.Layout) : Prop :=
  ∀ heap actions state, Invariant program objects retained owners original literals heap p .cs .reset →
    InitializationProtocol.ReferenceTrace .cs .reset actions state →
    (∀ action ∈ actions, action.Prepared objects retained original p access) →
    SourceContract model program objects retained owners original literals heap p access .cs .reset state actions

def SimulationCompiler [CInterface] (model : Solve.FMI3Model source) (program : Program Invocation) (header : CFenv.Header)
    (objects : Objects) (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (original literals : Heap) (p : Address) (buffers : StepEntry.Buffers) : Prop :=
  ∀ heap before final actions statuses,
    Persistent program objects retained owners original literals heap p →
    CSRun.Stored model.solve heap p buffers before → CSRun.ReferenceTrace header p buffers before actions final statuses →
    CSExecution model header program objects retained owners original literals heap p buffers before actions final statuses

variable [CInterface] {source : AST.Model} {model : Solve.FMI3Model source} {program : Program Invocation}
  {objects : Objects} {owners : SlotOwners.State objects.capacity}

theorem InitializationCompiler.interrupted
    (compiler : InitializationCompiler model program objects retained owners original literals p access)
    (invariant : Invariant program objects retained owners original literals heap p .cs .reset)
    (reference : InitializationProtocol.ReferenceTrace .cs .reset actions final)
    (prepared : ∀ action ∈ actions, action.Prepared objects retained original p access)
    (actual : InitializationProtocol.Interrupted program p access heap actions stop) :
    InitializationProtocol.SourcePrefix model p .cs .reset actions stop := by
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

theorem SimulationCompiler.interrupted
    (compiler : SimulationCompiler model program header objects retained owners original literals p buffers)
    (persistent : Persistent program objects retained owners original literals heap p)
    (stored : CSRun.Stored model.solve heap p buffers before)
    (reference : CSRun.ReferenceTrace header p buffers before actions final statuses)
    (actual : CSRun.Interrupted program p heap actions stop) :
    CSRun.SourcePrefix source header p buffers heap before actions stop := by
  have split := reference
  rw [actual.1] at split
  obtain ⟨middle, prefixStatuses, suffixStatuses, _, prefixTrace, suffixTrace⟩ := split.split
  have certified := compiler heap before middle stop.done prefixStatuses persistent stored prefixTrace
  obtain ⟨_, storedAtStop, persistentAtStop, _, _, _⟩ := certified.completed _ _ _ actual.2.1.completed
  have sample := storedAtStop.source_sample
  have sourceTrace := (certified.semantic _ _ _ _ actual.2.1).source_observations
  have pending := compiler stop.heap middle final (stop.pending :: stop.rest) suffixStatuses
    persistentAtStop storedAtStop suffixTrace
  have isStep := pending.faulted stop.pending stop.rest rfl actual.2.2
  cases suffixTrace with
  | cons changed _ => exact ⟨actual.1, middle, sourceTrace, sample, ⟨_, _, changed⟩, isStep⟩

end CSProtocol
end Rumoca.FMI3
end
