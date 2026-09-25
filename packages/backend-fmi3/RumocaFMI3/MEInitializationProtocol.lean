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
      (∀ action ∈ actions, action.Prepared objects retained original p access readers) →
      Admitted objects retained original p access addresses buffer readers (.finish actions state)
  | last : cycle.Admitted objects retained original p access addresses buffer readers →
      Admitted objects retained original p access addresses buffer readers (.last cycle)
  | next : cycle.Admitted objects retained original p access addresses buffer readers →
      Admitted objects retained original p access addresses buffer readers following →
      Admitted objects retained original p access addresses buffer readers (.next cycle following)

/-- Plans ending where fmi3Terminate is accepted or in Terminated. Every
simulation cycle ends there; a final initialization segment does after exit
or after an initialization error. -/
def Plan.Finished : Plan → Prop
  | .finish _ state => state.phase.Finished
  | .last _ => True
  | .next _ following => following.Finished

theorem Admitted.can_finish (admitted : Admitted objects retained original p access addresses buffer readers plan)
    (finished : plan.Finished) : LifecycleRelease.CanFinish .me plan.mode := by
  induction admitted with
  | finish _ _ => exact InitializationProtocol.Phase.can_finish .me _ finished
  | last admitted => exact admitted.can_finish
  | next _ _ ih => exact ih finished

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

noncomputable section
namespace Rumoca.FMI3.MEProtocol
open CMemory StaticFactory

/-- Host ownership of every initialization segment's caller cells. -/
def Plan.PoolSeparate (objects : Objects) : Plan → Prop
  | .finish actions _ => ∀ action ∈ actions, action.PoolSeparate objects
  | .last cycle => ∀ action ∈ cycle.initialization, action.PoolSeparate objects
  | .next cycle following => (∀ action ∈ cycle.initialization, action.PoolSeparate objects) ∧
      following.PoolSeparate objects

/-- Under host ownership, every cell of another instance record lies outside
all caller regions of an owned plan. -/
theorem Plan.outside_other (objects : Objects) {slot other : Fin objects.capacity} (different : other ≠ slot)
    (separate : access.Separate (objects.instances.index slot.val))
    (outputs : MENumericalHistory.CallerStorage heap (objects.instances.index slot.val) addresses buffer)
    (plan : Plan) (owned : plan.PoolSeparate objects)
    (inside : (objects.instances.index other.val).InRecord q) :
    plan.Outside (objects.instances.index slot.val) access addresses buffer q := by
  obtain ⟨pooled, notRecord, _⟩ := InitializationProtocol.other_instance objects different inside
  have field (name : String) : q ≠ (objects.instances.index slot.val).member name :=
    fun same => notRecord (same ▸ Address.member_in_record _ name)
  have step : MENumericalRun.Outside (objects.instances.index slot.val) addresses buffer q := by
    refine ⟨⟨⟨field "time", field "mode", field "eventTime", field "timeMin", field "lastCompleted", ?_⟩,
      fun same => notRecord (same ▸ (Address.member_in_record _ "model").member "x"), ?_⟩, field "stop", field "stopDefined"⟩
    · intro name member same
      subst same
      exact outputs.outside name member pooled
    · intro same
      subst same
      exact outputs.bufferOutside pooled
  induction plan with
  | finish actions _ => exact InitializationProtocol.untouched_other objects different separate owned inside
  | last cycle => exact ⟨InitializationProtocol.untouched_other objects different separate owned inside, step⟩
  | next cycle following ih =>
    exact ⟨InitializationProtocol.untouched_other objects different separate owned.1 inside, step, ih owned.2⟩

end Rumoca.FMI3.MEProtocol
end
