import Rumoca.FMI3CSMixedRun
import Rumoca.FMI3InitializationProtocolPrefixes
import RumocaFMI3.CSProtocolInterrupted

noncomputable section
namespace Rumoca.FMI3
open CMemory StaticFactory CCalls.Events

theorem CSMixedRun.Execution.recorded_source [CInterface] {source : AST.Model} {model : Solve.FMI3Model source}
    {program : Program Invocation} {objects : Objects} {owners : SlotOwners.State objects.capacity}
    (certified : CSMixedRun.Execution model header program objects retained owners original literals heap p buffers
      before actions final statuses readers)
    (actual : CSMixedRun.Recorded program p heap actions observed events after records) :
    CSMixedRun.SourceTrace source header p buffers heap before actions observed records after final := by
  obtain ⟨capability, enabled, _, trace⟩ := certified.trace
  exact trace.recorded_source actual

def CSMixedRun.SourcePrefix (source : AST.Model) (header : CFenv.Header) (p : Address) (buffers : StepEntry.Buffers)
    (heap : Heap) (before : CSRun.Reference) (actions : List CSMixedRun.Action) (stop : CSMixedRun.StopRecord) : Prop :=
  actions = stop.done ++ stop.pending :: stop.rest ∧
  ∃ reference, CSMixedRun.SourceTrace source header p buffers heap before stop.done stop.statuses stop.calls stop.heap reference ∧
    CSRun.SourceSample source p reference stop.heap ∧
    (∃ next status, CSMixedRun.Change header p buffers reference stop.pending next status) ∧
    stop.pending.MayBlock ∧ InitializationProtocol.Retention (CSMixedRun.loggingUpdate stop.done) p heap stop.heap

namespace CSProtocol
open InitializationProtocol (Invariant Persistent SourceContract ReadBank)
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
    CSRun.Stored model.solve heap p buffers before → CSMixedRun.ReferenceTrace header p buffers before actions final statuses →
    (∀ action ∈ actions, action.Prepared original) →
    (∀ action ∈ actions, ∀ q, action.ReaderRegion q → readers.Region q) →
    CSMixedRun.Execution model header program objects retained owners original literals heap p buffers before actions final statuses readers

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
    (reference : CSMixedRun.ReferenceTrace header p buffers before actions final statuses)
    (requests : ∀ action ∈ actions, action.Prepared original)
    (included : ∀ action ∈ actions, ∀ q, action.ReaderRegion q → readers.Region q)
    (actual : CSMixedRun.Interrupted program p heap actions stop) :
    CSMixedRun.SourcePrefix source header p buffers heap before actions stop := by
  have split := reference
  rw [actual.1] at split
  obtain ⟨middle, prefixStatuses, suffixStatuses, _, prefixTrace, suffixTrace⟩ := split.split
  have prefixMember {action : CSMixedRun.Action} (member : action ∈ stop.done) : action ∈ actions := by
    rw [actual.1]
    exact List.mem_append_left _ member
  have suffixMember {action : CSMixedRun.Action} (member : action ∈ stop.pending :: stop.rest) : action ∈ actions := by
    rw [actual.1]
    exact List.mem_append_right _ member
  have certified := compiler heap before middle stop.done prefixStatuses persistent stored prefixTrace
    (fun action member => requests action (prefixMember member)) (fun action member => included action (prefixMember member))
  obtain ⟨_, storedAtStop, persistentAtStop, keeps, _, _⟩ := certified.completed _ _ _ actual.2.1.completed
  have sourceTrace := certified.recorded_source actual.2.1
  have pending := compiler stop.heap middle final (stop.pending :: stop.rest) suffixStatuses
    persistentAtStop storedAtStop suffixTrace
    (fun action member => requests action (suffixMember member)) (fun action member => included action (suffixMember member))
  have mayBlock := pending.faulted stop.pending stop.rest rfl actual.2.2
  cases suffixTrace with
  | cons changed _ => exact ⟨actual.1, middle, sourceTrace, storedAtStop.source_sample, ⟨_, _, changed⟩, mayBlock, keeps⟩

end CSProtocol
end Rumoca.FMI3
end
