import RumocaFMI3.CSInitializationProtocol
import RumocaFMI3.CSRunInterrupted
import RumocaFMI3.InitializationProtocolInterrupted

noncomputable section
namespace Rumoca.FMI3.CSProtocol
open CMemory CCalls.Events

inductive StopRecord where
  | initialization (stop : InitializationProtocol.StopRecord)
  | simulation (stop : CSRun.StopRecord Invocation)
  | reset (heap : Heap)

/-- Retain all completed cycles and the observed prefix of the interrupted
segment. These constructors only sequence existing raw call relations. -/
inductive Interrupted [CInterface] (program : Program Invocation) (p : Address) (access : Float64Buffers.Layout) :
    Heap → Plan → List Record → StopRecord → Prop where
  | finish : InitializationProtocol.Interrupted program p access heap actions stop →
      Interrupted program p access heap (.finish actions state) [] (.initialization stop)
  | lastInitialization : InitializationProtocol.Interrupted program p access heap cycle.initialization stop →
      Interrupted program p access heap (.last cycle) [] (.initialization stop)
  | nextInitialization : InitializationProtocol.Interrupted program p access heap cycle.initialization stop →
      Interrupted program p access heap (.next cycle following) [] (.initialization stop)
  | lastSimulation : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      CSRun.Interrupted program p exited cycle.simulation stop →
      Interrupted program p access heap (.last cycle) [.initialization initial checkpoints exited] (.simulation stop)
  | nextSimulation : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      CSRun.Interrupted program p exited cycle.simulation stop →
      Interrupted program p access heap (.next cycle following) [.initialization initial checkpoints exited] (.simulation stop)
  | reset : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      CSRun.Recorded program p exited cycle.simulation statuses events simulated calls →
      (machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] simulated .done) (.wrong []) →
      Interrupted program p access heap (.next cycle following)
        [.initialization initial checkpoints exited, .simulation statuses events calls simulated] (.reset simulated)
  | later : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      CSRun.Recorded program p exited cycle.simulation statuses events simulated calls →
      (machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] simulated .done)
        (.terminates resetEvents ⟨resetStatus, resetHeap⟩) →
      Interrupted program p access resetHeap following records stop →
      Interrupted program p access heap (.next cycle following)
        (.initialization initial checkpoints exited :: .simulation statuses events calls simulated ::
          .reset resetEvents resetStatus resetHeap :: records) stop

variable [CInterface] {program : Program Invocation}

theorem Interrupted.stopped (actual : Interrupted program p access heap plan records stop) :
    Stopped program p access heap plan := by
  induction actual with
  | finish stopped => exact .finish stopped.stopped
  | lastInitialization stopped => exact .lastInitialization stopped.stopped
  | nextInitialization stopped => exact .nextInitialization stopped.stopped
  | lastSimulation initialized stopped => exact .lastSimulation initialized stopped.stopped
  | nextSimulation initialized stopped => exact .nextSimulation initialized stopped.stopped
  | reset initialized simulated called => exact .reset initialized simulated called
  | later initialized simulated called _ ih => exact .later initialized simulated called ih

theorem Stopped.interrupted (actual : Stopped program p access heap plan) :
    ∃ records stop, Interrupted program p access heap plan records stop := by
  induction actual with
  | finish stopped =>
    obtain ⟨stop, interrupted⟩ := stopped.interrupted
    exact ⟨[], _, .finish interrupted⟩
  | lastInitialization stopped =>
    obtain ⟨stop, interrupted⟩ := stopped.interrupted
    exact ⟨[], _, .lastInitialization interrupted⟩
  | nextInitialization stopped =>
    obtain ⟨stop, interrupted⟩ := stopped.interrupted
    exact ⟨[], _, .nextInitialization interrupted⟩
  | lastSimulation initialized stopped =>
    obtain ⟨stop, interrupted⟩ := stopped.interrupted
    exact ⟨_, _, .lastSimulation initialized interrupted⟩
  | nextSimulation initialized stopped =>
    obtain ⟨stop, interrupted⟩ := stopped.interrupted
    exact ⟨_, _, .nextSimulation initialized interrupted⟩
  | reset initialized simulated called => exact ⟨_, _, .reset initialized simulated called⟩
  | later initialized simulated called _ ih =>
    obtain ⟨records, stop, interrupted⟩ := ih
    exact ⟨_, stop, .later initialized simulated called interrupted⟩

theorem interrupted_iff : (∃ records stop, Interrupted program p access heap plan records stop) ↔
    Stopped program p access heap plan :=
  ⟨fun ⟨_, _, actual⟩ => actual.stopped, Stopped.interrupted⟩

end Rumoca.FMI3.CSProtocol
end
