import RumocaFMI3.InitializationMESimulation
import RumocaFMI3.InitializationProtocolRestart
import RumocaFMI3.InitializationProtocolLifetime
import RumocaFMI3.MEMixedLifecycle
import RumocaFMI3.MEMixedInterrupted

noncomputable section
namespace Rumoca.FMI3.MEProtocol
open CMemory StaticFactory CCalls.Events
variable {readers : InitializationProtocol.ReadBank}

/-- Reference states constrain admission, while raw executions retain the
actual observations of the requested initialization and ME calls. -/
structure Cycle where
  initialization : List InitializationProtocol.Action
  state : InitializationProtocol.State
  args : Initialization.Arguments
  simulation : List MEMixedRun.Action
  final : MENumericalHistory.ReferenceState
  finalClock : Time.Clock

inductive Plan where
  | finish (initialization : List InitializationProtocol.Action) (state : InitializationProtocol.State)
  | last (cycle : Cycle)
  | next (cycle : Cycle) (following : Plan)

def Plan.mode : Plan → Mode
  | .finish _ state => state.phase.mode .me
  | .last cycle => cycle.final.control.mode
  | .next _ following => following.mode

/-- Simulation updates follow the initialization updates in each cycle. -/
def Cycle.loggingUpdate (cycle : Cycle) : Option Bool :=
  (MEMixedRun.loggingUpdate cycle.simulation).orElse fun _ => InitializationProtocol.loggingUpdate cycle.initialization

/-- Compose every initialization and simulation segment in execution order. -/
def Plan.loggingUpdate : Plan → Option Bool
  | .finish actions _ => InitializationProtocol.loggingUpdate actions
  | .last cycle => cycle.loggingUpdate
  | .next cycle following => following.loggingUpdate.orElse
      (fun _ => cycle.loggingUpdate)

structure Cycle.Admitted (cycle : Cycle) (objects : Objects) (retained : Address → Prop)
    (original : Heap) (p : Address) (access : Float64Buffers.Layout)
    (addresses : String → Address) (buffer : Address) (readers : InitializationProtocol.ReadBank) : Prop where
  initialization : InitializationProtocol.ReferenceTrace .me .reset cycle.initialization cycle.state
  requests : ∀ action ∈ cycle.initialization, action.Prepared objects retained original p access readers
  initialized : cycle.state.phase = .initialized cycle.args
  simulation : MEMixedRun.ReferenceTrace buffer (InitializationProtocol.meReference cycle.state cycle.args)
    (Time.Clock.initial cycle.args.start) cycle.simulation cycle.final cycle.finalClock
  resources : ∀ action ∈ cycle.simulation, action.Prepared objects original addresses buffer
  regions : ∀ action ∈ cycle.simulation, ∀ q, action.CallerRegion q → Float64Rejection.Protected objects retained q
  readerSafe : ∀ action ∈ cycle.simulation, ∀ q, readers.Region q → ¬ action.CallerRegion q
  readerIncluded : ∀ action ∈ cycle.simulation, ∀ q, action.ReaderRegion q → readers.Region q

theorem Cycle.Admitted.can_finish {cycle : Cycle} (admitted : cycle.Admitted objects retained original p access addresses buffer readers) :
    LifecycleRelease.CanFinish .me cycle.final.control.mode :=
  admitted.simulation.can_finish (Or.inl (by simp [InitializationProtocol.meReference,
    MENumericalHistory.ReferenceState.initial, MEHistory.ReferenceState.initial, Reference.Allowed]))

inductive Admitted (objects : Objects) (retained : Address → Prop) (original : Heap)
    (p : Address) (access : Float64Buffers.Layout) (addresses : String → Address) (buffer : Address) (readers : InitializationProtocol.ReadBank) : Plan → Prop where
  | finish : InitializationProtocol.ReferenceTrace .me .reset actions state →
      (∀ action ∈ actions, action.Prepared objects retained original p access readers) → state.phase.Finished →
      Admitted objects retained original p access addresses buffer readers (.finish actions state)
  | last : cycle.Admitted objects retained original p access addresses buffer readers →
      Admitted objects retained original p access addresses buffer readers (.last cycle)
  | next : cycle.Admitted objects retained original p access addresses buffer readers →
      Admitted objects retained original p access addresses buffer readers following →
      Admitted objects retained original p access addresses buffer readers (.next cycle following)

inductive Record where
  | initialization (observed : List (Float64Access.Observation Invocation)) (checkpoints : List Heap) (heap : Heap)
  | simulation (observed : List (MENumericalHistory.Observation Invocation)) (epochs : List MENumericalRun.Epoch) (heap : Heap)
  | reset (events : List Invocation) (status : Value) (heap : Heap)

/-- Sequence existing raw histories and actual reset calls. No expected
status, reference state or callback return restricts these constructors. -/
inductive Completed [CInterface] (program : Program Invocation) (p : Address)
    (access : Float64Buffers.Layout) (addresses : String → Address) (buffer : Address) :
    Heap → Plan → List Record → Heap → Prop where
  | finish : InitializationProtocol.Completed program p access heap actions observed after checkpoints →
      Completed program p access addresses buffer heap (.finish actions state) [.initialization observed checkpoints after] after
  | last : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      MEMixedRun.Completed program p addresses buffer exited cycle.simulation observed after epochs →
      Completed program p access addresses buffer heap (.last cycle)
        [.initialization initial checkpoints exited, .simulation observed epochs after] after
  | next : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      MEMixedRun.Completed program p addresses buffer exited cycle.simulation observed simulated epochs →
      (machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] simulated .done)
        (.terminates resetEvents ⟨resetStatus, resetHeap⟩) →
      Completed program p access addresses buffer resetHeap following records after →
      Completed program p access addresses buffer heap (.next cycle following)
        (.initialization initial checkpoints exited :: .simulation observed epochs simulated ::
          .reset resetEvents resetStatus resetHeap :: records) after

inductive Stopped [CInterface] (program : Program Invocation) (p : Address)
    (access : Float64Buffers.Layout) (addresses : String → Address) (buffer : Address) : Heap → Plan → Prop where
  | finish : InitializationProtocol.Stopped program p access heap actions →
      Stopped program p access addresses buffer heap (.finish actions state)
  | lastInitialization : InitializationProtocol.Stopped program p access heap cycle.initialization →
      Stopped program p access addresses buffer heap (.last cycle)
  | nextInitialization : InitializationProtocol.Stopped program p access heap cycle.initialization →
      Stopped program p access addresses buffer heap (.next cycle following)
  | lastSimulation : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      MEMixedRun.Stopped program p addresses buffer exited cycle.simulation →
      Stopped program p access addresses buffer heap (.last cycle)
  | nextSimulation : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      MEMixedRun.Stopped program p addresses buffer exited cycle.simulation →
      Stopped program p access addresses buffer heap (.next cycle following)
  | reset : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      MEMixedRun.Completed program p addresses buffer exited cycle.simulation observed simulated epochs →
      (machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] simulated .done) (.wrong []) →
      Stopped program p access addresses buffer heap (.next cycle following)
  | later : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      MEMixedRun.Completed program p addresses buffer exited cycle.simulation observed simulated epochs →
      (machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] simulated .done)
        (.terminates resetEvents ⟨resetStatus, resetHeap⟩) →
      Stopped program p access addresses buffer resetHeap following →
      Stopped program p access addresses buffer heap (.next cycle following)

def Plan.Outside (plan : Plan) (p : Address) (access : Float64Buffers.Layout)
    (addresses : String → Address) (buffer q : Address) : Prop :=
  match plan with
  | .finish actions _ => InitializationProtocol.Untouched p access actions q
  | .last cycle => InitializationProtocol.Untouched p access cycle.initialization q ∧ MENumericalRun.Outside p addresses buffer q
  | .next cycle following => InitializationProtocol.Untouched p access cycle.initialization q ∧
      MENumericalRun.Outside p addresses buffer q ∧ following.Outside p access addresses buffer q

theorem Plan.Outside.not_record {plan : Plan} {p q : Address}
    (outside : plan.Outside p access addresses buffer q) : ¬ p.InRecord q := by
  cases plan with
  | finish _ _ => exact outside.1
  | last _ => exact outside.1.1
  | next _ _ => exact outside.1.1

end Rumoca.FMI3.MEProtocol
end
