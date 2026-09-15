import RumocaFMI3.CSMixedHandoff
import RumocaFMI3.CSMixedLifecycle
import RumocaFMI3.CSMixedRecords
import RumocaFMI3.InitializationProtocolLifetime

noncomputable section
namespace Rumoca.FMI3.CSProtocol
open CMemory StaticFactory CCalls.Events

/-- One initialization/simulation segment. These reference values constrain
admission; the raw execution relation uses only the requested calls. -/
structure Cycle where
  initialization : List InitializationProtocol.Action
  state : InitializationProtocol.State
  args : Initialization.Arguments
  simulation : List CSMixedRun.Action
  final : CSRun.Reference
  statuses : List Int

inductive Plan where
  | finish (initialization : List InitializationProtocol.Action) (state : InitializationProtocol.State)
  | last (cycle : Cycle)
  | next (cycle : Cycle) (following : Plan)

def Plan.mode : Plan → Mode
  | .finish _ state => state.phase.mode .cs
  | .last cycle => cycle.final.mode
  | .next _ following => following.mode

/-- Each cycle composes the initialization and simulation logging updates. -/
def Cycle.loggingUpdate (cycle : Cycle) : Option Bool :=
  (CSMixedRun.loggingUpdate cycle.simulation).orElse
    (fun _ => InitializationProtocol.loggingUpdate cycle.initialization)

/-- The final update includes every initialization and simulation segment. -/
def Plan.loggingUpdate : Plan → Option Bool
  | .finish actions _ => InitializationProtocol.loggingUpdate actions
  | .last cycle => cycle.loggingUpdate
  | .next cycle following => following.loggingUpdate.orElse
      (fun _ => cycle.loggingUpdate)

def Cycle.Admitted (cycle : Cycle) (header : CFenv.Header) (objects : Objects)
    (retained : Address → Prop) (original : Heap) (p : Address)
    (access : Float64Buffers.Layout) (buffers : StepEntry.Buffers) (readers : InitializationProtocol.ReadBank) : Prop :=
  InitializationProtocol.ReferenceTrace .cs .reset cycle.initialization cycle.state ∧
  (∀ action ∈ cycle.initialization, action.Prepared objects retained original p access readers) ∧
  cycle.state.phase = .initialized cycle.args ∧
  CSMixedRun.ReferenceTrace header p buffers (InitializationProtocol.csReference cycle.state cycle.args)
    cycle.simulation cycle.final cycle.statuses ∧
  (∀ action ∈ cycle.simulation, action.Prepared original) ∧
  (∀ action ∈ cycle.simulation, ∀ q, action.ReaderRegion q → readers.Region q)

inductive Admitted (header : CFenv.Header) (objects : Objects) (retained : Address → Prop)
    (original : Heap) (p : Address) (access : Float64Buffers.Layout) (buffers : StepEntry.Buffers) (readers : InitializationProtocol.ReadBank) : Plan → Prop where
  | finish : InitializationProtocol.ReferenceTrace .cs .reset actions state →
      (∀ action ∈ actions, action.Prepared objects retained original p access readers) → state.phase.Finished →
      Admitted header objects retained original p access buffers readers (.finish actions state)
  | last : cycle.Admitted header objects retained original p access buffers readers →
      Admitted header objects retained original p access buffers readers (.last cycle)
  | next : cycle.Admitted header objects retained original p access buffers readers →
      Admitted header objects retained original p access buffers readers following →
      Admitted header objects retained original p access buffers readers (.next cycle following)

/-- Keep every segment's actual observations and heap; later resets cannot
erase the source initialization checkpoints or earlier numerical samples. -/
inductive Record where
  | initialization (observed : List (Float64Access.Observation Invocation)) (checkpoints : List Heap) (heap : Heap)
  | simulation (statuses : List Value) (events : List Invocation) (calls : List CSMixedRun.CallRecord) (heap : Heap)
  | reset (events : List Invocation) (status : Value) (heap : Heap)

/-- This is sequencing of the existing raw relations, not another numerical
or C semantics. In particular reset has an arbitrary raw result value. -/
inductive Completed [CInterface] (program : Program Invocation) (p : Address) (access : Float64Buffers.Layout) :
    Heap → Plan → List Record → Heap → Prop where
  | finish : InitializationProtocol.Completed program p access heap actions observed after checkpoints →
      Completed program p access heap (.finish actions state) [.initialization observed checkpoints after] after
  | last : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      CSMixedRun.Recorded program p exited cycle.simulation statuses events after calls →
      Completed program p access heap (.last cycle)
        [.initialization initial checkpoints exited, .simulation statuses events calls after] after
  | next : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      CSMixedRun.Recorded program p exited cycle.simulation statuses events simulated calls →
      (machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] simulated .done)
        (.terminates resetEvents ⟨resetStatus, resetHeap⟩) →
      Completed program p access resetHeap following records after →
      Completed program p access heap (.next cycle following)
        (.initialization initial checkpoints exited :: .simulation statuses events calls simulated ::
          .reset resetEvents resetStatus resetHeap :: records) after

inductive Stopped [CInterface] (program : Program Invocation) (p : Address) (access : Float64Buffers.Layout) :
    Heap → Plan → Prop where
  | finish : InitializationProtocol.Stopped program p access heap actions → Stopped program p access heap (.finish actions state)
  | lastInitialization : InitializationProtocol.Stopped program p access heap cycle.initialization →
      Stopped program p access heap (.last cycle)
  | nextInitialization : InitializationProtocol.Stopped program p access heap cycle.initialization →
      Stopped program p access heap (.next cycle following)
  | lastSimulation : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      CSMixedRun.Stopped program p exited cycle.simulation → Stopped program p access heap (.last cycle)
  | nextSimulation : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      CSMixedRun.Stopped program p exited cycle.simulation → Stopped program p access heap (.next cycle following)
  | reset : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      CSMixedRun.Recorded program p exited cycle.simulation statuses events simulated calls →
      (machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] simulated .done) (.wrong []) →
      Stopped program p access heap (.next cycle following)
  | later : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      CSMixedRun.Recorded program p exited cycle.simulation statuses events simulated calls →
      (machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] simulated .done)
        (.terminates resetEvents ⟨resetStatus, resetHeap⟩) →
      Stopped program p access resetHeap following → Stopped program p access heap (.next cycle following)

def Plan.Outside (plan : Plan) (p : Address) (access : Float64Buffers.Layout)
    (buffers : StepEntry.Buffers) (q : Address) : Prop :=
  match plan with
  | .finish actions _ => InitializationProtocol.Untouched p access actions q
  | .last cycle => InitializationProtocol.Untouched p access cycle.initialization q ∧ CSRun.Outside p buffers q
  | .next cycle following => InitializationProtocol.Untouched p access cycle.initialization q ∧
      CSRun.Outside p buffers q ∧ following.Outside p access buffers q

theorem Plan.Outside.not_record {plan : Plan} {p q : Address}
    (outside : plan.Outside p access buffers q) : ¬ p.InRecord q := by
  cases plan with
  | finish _ _ => exact outside.1
  | last _ => exact outside.1.1
  | next _ _ => exact outside.1.1

theorem Cycle.Admitted.can_finish {cycle : Cycle} (admitted : cycle.Admitted header objects retained original p access buffers readers) :
    CSRun.CanFinish cycle.final.mode :=
  admitted.2.2.2.1.can_finish (Or.inl rfl)

end Rumoca.FMI3.CSProtocol
end
