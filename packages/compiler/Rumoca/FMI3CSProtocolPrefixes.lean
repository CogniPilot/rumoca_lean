import Rumoca.FMI3InitializationProtocolPrefixes
import RumocaFMI3.CSRunInterrupted
import RumocaFMI3.InitializationProtocolInterrupted
import RumocaFMI3.InitializationSimulation
import Rumoca.FMI3CSRunRecords

noncomputable section
namespace Rumoca.FMI3
open CMemory StaticFactory CCalls.Events

def CSRun.SourcePrefix (source : AST.Model) (header : CFenv.Header) (p : Address) (buffers : StepEntry.Buffers)
    (heap : Heap) (before : CSRun.Reference) (actions : List CSRun.Action) (stop : CSRun.StopRecord Invocation) : Prop :=
  actions = stop.done ++ stop.pending :: stop.rest ∧
  ∃ reference, CSRun.SourceTrace source header p buffers heap before stop.done stop.statuses stop.calls stop.heap reference ∧
    CSRun.SourceSample source p reference stop.heap ∧
    (∃ next status, CSRun.Change header p buffers reference stop.pending next status) ∧
    ∃ request outputs, stop.pending = .step request outputs

namespace CSProtocol
open InitializationProtocol (Invariant Persistent CSExecution SourceContract ReadBank)
variable {readers : ReadBank}

def InitializationCompiler [CInterface] (model : Solve.FMI3Model source) (program : Program Invocation) (objects : Objects)
    (retained : Address → Prop) (owners : SlotOwners.State objects.capacity) (original literals : Heap)
    (p : Address) (access : Float64Buffers.Layout) (readers : ReadBank) : Prop :=
  ∀ heap actions state, Invariant program objects retained owners original literals heap p .cs .reset readers →
    InitializationProtocol.ReferenceTrace .cs .reset actions state →
    (∀ action ∈ actions, action.Prepared objects retained original p access readers) →
    SourceContract model program objects retained owners original literals heap p access .cs .reset state actions readers

def SimulationCompiler [CInterface] (model : Solve.FMI3Model source) (program : Program Invocation) (header : CFenv.Header)
    (objects : Objects) (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (original literals : Heap) (p : Address) (buffers : StepEntry.Buffers) (readers : ReadBank) : Prop :=
  ∀ heap before final actions statuses,
    Persistent program objects retained owners original literals heap p readers →
    CSRun.Stored model.solve heap p buffers before → CSRun.ReferenceTrace header p buffers before actions final statuses →
    CSExecution model header program objects retained owners original literals heap p buffers before actions final statuses readers

variable [CInterface] {source : AST.Model} {model : Solve.FMI3Model source} {program : Program Invocation}
  {objects : Objects} {owners : SlotOwners.State objects.capacity}

theorem InitializationCompiler.interrupted
    (compiler : InitializationCompiler model program objects retained owners original literals p access readers)
    (invariant : Invariant program objects retained owners original literals heap p .cs .reset readers)
    (reference : InitializationProtocol.ReferenceTrace .cs .reset actions final)
    (prepared : ∀ action ∈ actions, action.Prepared objects retained original p access readers)
    (actual : InitializationProtocol.Interrupted program p access heap actions stop) :
    InitializationProtocol.SourcePrefix model p .cs .reset actions stop :=
  InitializationProtocol.SourcePrefix.of_compiler compiler invariant reference prepared actual

theorem SimulationCompiler.interrupted
    (compiler : SimulationCompiler model program header objects retained owners original literals p buffers readers)
    (persistent : Persistent program objects retained owners original literals heap p readers)
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
