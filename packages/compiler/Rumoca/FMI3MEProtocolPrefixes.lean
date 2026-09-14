import Rumoca.FMI3InitializationProtocolPrefixes
import Rumoca.FMI3MEMixedRun
import RumocaFMI3.InitializationMESimulation

noncomputable section
namespace Rumoca.FMI3.MEProtocol
open CMemory StaticFactory CCalls.Events
open InitializationProtocol (Invariant Persistent MEExecution SourceContract)

def InitializationCompiler [CInterface] (model : Solve.Model source) (program : Program Invocation) (objects : Objects)
    (retained : Address → Prop) (owners : SlotOwners.State objects.capacity) (original literals : Heap)
    (p : Address) (access : Float64Buffers.Layout) : Prop :=
  ∀ heap actions state, Invariant program objects retained owners original literals heap p .me .reset →
    InitializationProtocol.ReferenceTrace .me .reset actions state →
    (∀ action ∈ actions, action.Prepared objects retained original p access) →
    SourceContract model.prepareFMI3 program objects retained owners original literals heap p access .me .reset state actions

def SimulationCompiler [CInterface] (model : Solve.Model source) (program : Program Invocation)
    (objects : Objects) (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (original literals : Heap) (p : Address) (addresses : String → Address) (buffer : Address) : Prop :=
  ∀ heap before final clock finalClock actions,
    Persistent program objects retained owners original literals heap p →
    MENumericalHistory.Stored heap p clock before addresses buffer → Reset.Storage heap p →
    MEMixedRun.ReferenceTrace buffer before clock actions final finalClock →
    MEExecution model.prepareFMI3 program objects retained owners original literals heap p addresses buffer before clock actions final finalClock

variable [CInterface] {source : AST.Model} {model : Solve.Model source} {program : Program Invocation}
  {objects : Objects} {owners : SlotOwners.State objects.capacity}

theorem InitializationCompiler.interrupted
    (compiler : InitializationCompiler model program objects retained owners original literals p access)
    (invariant : Invariant program objects retained owners original literals heap p .me .reset)
    (reference : InitializationProtocol.ReferenceTrace .me .reset actions final)
    (prepared : ∀ action ∈ actions, action.Prepared objects retained original p access)
    (actual : InitializationProtocol.Interrupted program p access heap actions stop) :
    InitializationProtocol.SourcePrefix model.prepareFMI3 p .me .reset actions stop :=
  InitializationProtocol.SourcePrefix.of_compiler compiler invariant reference prepared actual

theorem SimulationCompiler.interrupted
    (compiler : SimulationCompiler model program objects retained owners original literals p addresses buffer)
    (persistent : Persistent program objects retained owners original literals heap p)
    (stored : MENumericalHistory.Stored heap p clock before addresses buffer) (reset : Reset.Storage heap p)
    (reference : MEMixedRun.ReferenceTrace buffer before clock actions final finalClock)
    (actual : MEMixedRun.Interrupted program p addresses buffer heap actions stop) :
    MEMixedRun.SourcePrefix source p addresses buffer before clock actions stop := by
  have split := reference
  rw [actual.1] at split
  obtain ⟨middle, middleClock, prefixTrace, suffixTrace⟩ := split.split
  have certified := compiler heap before middle clock middleClock stop.done persistent stored reset prefixTrace
  obtain ⟨storedAtStop, resetAtStop, persistentAtStop, _, _, _⟩ := certified.completed _ _ _ actual.2.1
  obtain ⟨config, traced⟩ := certified.trace
  obtain ⟨observations, checkpoints⟩ := traced.source model actual.2.1
  have pending := compiler stop.heap middle final middleClock finalClock (stop.pending :: stop.rest)
    persistentAtStop storedAtStop resetAtStop suffixTrace
  have isRejection := pending.faulted stop.pending stop.rest rfl actual.2.2
  cases suffixTrace with
  | cons allowed _ => exact ⟨actual.1, observations, checkpoints, middle, middleClock,
      prefixTrace, storedAtStop, allowed, isRejection⟩

end Rumoca.FMI3.MEProtocol
end
