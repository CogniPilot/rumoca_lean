import Rumoca.FMI3InitializationProtocolPrefixes
import Rumoca.FMI3MEMixedRun
import RumocaFMI3.InitializationMESimulation

noncomputable section
namespace Rumoca.FMI3.MEProtocol
open CMemory StaticFactory CCalls.Events
open InitializationProtocol (Invariant Persistent MEExecution SourceContract ReadBank)
variable {readers : ReadBank}

def InitializationCompiler [CInterface] (model : Solve.Model source) (program : Program Invocation) (objects : Objects)
    (retained : Address → Prop) (owners : SlotOwners.State objects.capacity) (original literals : Heap)
    (p : Address) (access : Float64Buffers.Layout) (readers : ReadBank) : Prop :=
  ∀ heap actions state, Invariant program objects retained owners original literals heap p .me .reset readers →
    InitializationProtocol.ReferenceTrace .me .reset actions state →
    (∀ action ∈ actions, action.Prepared objects retained original p access readers) →
    SourceContract model.prepareFMI3 program objects retained owners original literals heap p access .me .reset state actions readers

def SimulationCompiler [CInterface] (model : Solve.Model source) (program : Program Invocation)
    (objects : Objects) (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (original literals : Heap) (p : Address) (addresses : String → Address) (buffer : Address) (readers : ReadBank) : Prop :=
  ∀ heap before final clock finalClock actions,
    Persistent program objects retained owners original literals heap p readers →
    MENumericalHistory.Stored heap p clock before addresses buffer → Reset.Storage heap p →
    MEMixedRun.ReferenceTrace buffer before clock actions final finalClock →
    (∀ action ∈ actions, action.Prepared objects original addresses buffer) →
    (∀ action ∈ actions, ∀ q, action.CallerRegion q → Float64Rejection.Protected objects retained q) →
    (∀ action ∈ actions, ∀ q, readers.Region q → ¬ action.CallerRegion q) →
    (∀ action ∈ actions, ∀ q, action.ReaderRegion q → readers.Region q) →
    MEExecution model.prepareFMI3 program objects retained owners original literals heap p addresses buffer before clock actions final finalClock readers

variable [CInterface] {source : AST.Model} {model : Solve.Model source} {program : Program Invocation}
  {objects : Objects} {owners : SlotOwners.State objects.capacity}

theorem InitializationCompiler.interrupted
    (compiler : InitializationCompiler model program objects retained owners original literals p access readers)
    (invariant : Invariant program objects retained owners original literals heap p .me .reset readers)
    (reference : InitializationProtocol.ReferenceTrace .me .reset actions final)
    (prepared : ∀ action ∈ actions, action.Prepared objects retained original p access readers)
    (actual : InitializationProtocol.Interrupted program p access heap actions stop) :
    InitializationProtocol.SourcePrefix model.prepareFMI3 p .me .reset actions stop :=
  InitializationProtocol.SourcePrefix.of_compiler compiler invariant reference prepared actual

theorem SimulationCompiler.interrupted
    (compiler : SimulationCompiler model program objects retained owners original literals p addresses buffer readers)
    (persistent : Persistent program objects retained owners original literals heap p readers)
    (stored : MENumericalHistory.Stored heap p clock before addresses buffer) (reset : Reset.Storage heap p)
    (reference : MEMixedRun.ReferenceTrace buffer before clock actions final finalClock)
    (requests : ∀ action ∈ actions, action.Prepared objects original addresses buffer)
    (regions : ∀ action ∈ actions, ∀ q, action.CallerRegion q → Float64Rejection.Protected objects retained q)
    (readerSafe : ∀ action ∈ actions, ∀ q, readers.Region q → ¬ action.CallerRegion q)
    (included : ∀ action ∈ actions, ∀ q, action.ReaderRegion q → readers.Region q)
    (actual : MEMixedRun.Interrupted program p addresses buffer heap actions stop) :
    ∃ capability enabled, MEMixedRun.SourcePrefix model capability enabled heap p addresses buffer before clock actions stop := by
  have split := reference
  rw [actual.1] at split
  rw [actual.1] at requests regions readerSafe included
  obtain ⟨middle, middleClock, prefixTrace, suffixTrace⟩ := split.split
  have certified := compiler heap before middle clock middleClock stop.done persistent stored reset prefixTrace
    (fun action member => requests action (List.mem_append_left _ member))
    (fun action member => regions action (List.mem_append_left _ member))
    (fun action member => readerSafe action (List.mem_append_left _ member))
    (fun action member => included action (List.mem_append_left _ member))
  obtain ⟨storedAtStop, resetAtStop, persistentAtStop, _, _, _⟩ := certified.completed _ _ _ actual.2.1
  obtain ⟨capability, enabled, _, traced⟩ := certified.trace
  obtain ⟨_, _, configuredAtStop, retainedAtStop, _⟩ := traced.completed actual.2.1
  obtain ⟨observations, checkpoints⟩ := traced.source model actual.2.1
  have pending := compiler stop.heap middle final middleClock finalClock (stop.pending :: stop.rest)
    persistentAtStop storedAtStop resetAtStop suffixTrace
    (fun action member => requests action (List.mem_append_right _ member))
    (fun action member => regions action (List.mem_append_right _ member))
    (fun action member => readerSafe action (List.mem_append_right _ member))
    (fun action member => included action (List.mem_append_right _ member))
  have isRejection := pending.faulted stop.pending stop.rest rfl actual.2.2
  cases suffixTrace with
  | cons allowed _ => exact ⟨capability, enabled, actual.1, configuredAtStop, retainedAtStop, observations, checkpoints, middle, middleClock,
      prefixTrace, storedAtStop, allowed, isRejection⟩

end Rumoca.FMI3.MEProtocol
end
