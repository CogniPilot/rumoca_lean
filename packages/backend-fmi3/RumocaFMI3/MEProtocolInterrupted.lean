import RumocaFMI3.MEInitializationProtocol
import RumocaFMI3.MEMixedInterrupted
import RumocaFMI3.InitializationProtocolInterrupted

noncomputable section
namespace Rumoca.FMI3.MEProtocol
open CMemory CCalls.Events

inductive StopRecord where
  | initialization (stop : InitializationProtocol.StopRecord)
  | simulation (stop : MEMixedRun.StopRecord)
  | reset (heap : Heap)

/-- Retain all completed cycles and the observed prefix of the interrupted
segment. These constructors only sequence existing raw call relations. -/
inductive Interrupted [CInterface] (program : Program Invocation) (p : Address) (access : Float64Buffers.Layout)
    (addresses : String → Address) (buffer : Address) :
    Heap → Plan → List Record → StopRecord → Prop where
  | finish : InitializationProtocol.Interrupted program p access heap actions stop →
      Interrupted program p access addresses buffer heap (.finish actions state) [] (.initialization stop)
  | lastInitialization : InitializationProtocol.Interrupted program p access heap cycle.initialization stop →
      Interrupted program p access addresses buffer heap (.last cycle) [] (.initialization stop)
  | nextInitialization : InitializationProtocol.Interrupted program p access heap cycle.initialization stop →
      Interrupted program p access addresses buffer heap (.next cycle following) [] (.initialization stop)
  | lastSimulation : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      MEMixedRun.Interrupted program p addresses buffer exited cycle.simulation stop →
      Interrupted program p access addresses buffer heap (.last cycle) [.initialization initial checkpoints exited] (.simulation stop)
  | nextSimulation : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      MEMixedRun.Interrupted program p addresses buffer exited cycle.simulation stop →
      Interrupted program p access addresses buffer heap (.next cycle following) [.initialization initial checkpoints exited] (.simulation stop)
  | reset : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      MEMixedRun.Completed program p addresses buffer exited cycle.simulation observed simulated epochs →
      (machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] simulated .done) (.wrong []) →
      Interrupted program p access addresses buffer heap (.next cycle following)
        [.initialization initial checkpoints exited, .simulation observed epochs simulated] (.reset simulated)
  | later : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      MEMixedRun.Completed program p addresses buffer exited cycle.simulation observed simulated epochs →
      (machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] simulated .done)
        (.terminates resetEvents ⟨resetStatus, resetHeap⟩) →
      Interrupted program p access addresses buffer resetHeap following records stop →
      Interrupted program p access addresses buffer heap (.next cycle following)
        (.initialization initial checkpoints exited :: .simulation observed epochs simulated ::
          .reset resetEvents resetStatus resetHeap :: records) stop

variable [CInterface] {program : Program Invocation}

theorem Interrupted.stopped (actual : Interrupted program p access addresses buffer heap plan records stop) :
    Stopped program p access addresses buffer heap plan := by
  induction actual with
  | finish stopped => exact .finish stopped.stopped
  | lastInitialization stopped => exact .lastInitialization stopped.stopped
  | nextInitialization stopped => exact .nextInitialization stopped.stopped
  | lastSimulation initialized stopped => exact .lastSimulation initialized stopped.stopped
  | nextSimulation initialized stopped => exact .nextSimulation initialized stopped.stopped
  | reset initialized simulated called => exact .reset initialized simulated called
  | later initialized simulated called _ ih => exact .later initialized simulated called ih

theorem Stopped.interrupted (actual : Stopped program p access addresses buffer heap plan) :
    ∃ records stop, Interrupted program p access addresses buffer heap plan records stop := by
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

theorem interrupted_iff : (∃ records stop, Interrupted program p access addresses buffer heap plan records stop) ↔
    Stopped program p access addresses buffer heap plan :=
  ⟨fun ⟨_, _, actual⟩ => actual.stopped, Stopped.interrupted⟩

end Rumoca.FMI3.MEProtocol
end
