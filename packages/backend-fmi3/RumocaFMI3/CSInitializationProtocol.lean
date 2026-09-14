import RumocaFMI3.InitializationSimulation
import RumocaFMI3.InitializationProtocolRestart
import RumocaFMI3.InitializationProtocolLifetime
import RumocaFMI3.CSRunFinish

noncomputable section
namespace Rumoca.FMI3.CSProtocol
open CMemory StaticFactory CCalls.Events

/-- One initialization/simulation segment. These reference values constrain
admission; the raw execution relation uses only the requested calls. -/
structure Cycle where
  initialization : List InitializationProtocol.Action
  state : InitializationProtocol.State
  args : Initialization.Arguments
  simulation : List CSRun.Action
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

def Cycle.Admitted (cycle : Cycle) (header : CFenv.Header) (objects : Objects)
    (retained : Address → Prop) (original : Heap) (p : Address)
    (access : Float64Buffers.Layout) (buffers : StepEntry.Buffers) : Prop :=
  InitializationProtocol.ReferenceTrace .cs .reset cycle.initialization cycle.state ∧
  (∀ action ∈ cycle.initialization, action.Prepared objects retained original p access) ∧
  cycle.state.phase = .initialized cycle.args ∧
  CSRun.ReferenceTrace header p buffers (InitializationProtocol.csReference cycle.state cycle.args)
    cycle.simulation cycle.final cycle.statuses

inductive Admitted (header : CFenv.Header) (objects : Objects) (retained : Address → Prop)
    (original : Heap) (p : Address) (access : Float64Buffers.Layout) (buffers : StepEntry.Buffers) : Plan → Prop where
  | finish : InitializationProtocol.ReferenceTrace .cs .reset actions state →
      (∀ action ∈ actions, action.Prepared objects retained original p access) → state.phase.Finished →
      Admitted header objects retained original p access buffers (.finish actions state)
  | last : cycle.Admitted header objects retained original p access buffers →
      Admitted header objects retained original p access buffers (.last cycle)
  | next : cycle.Admitted header objects retained original p access buffers →
      Admitted header objects retained original p access buffers following →
      Admitted header objects retained original p access buffers (.next cycle following)

/-- Keep every segment's actual observations and heap; later resets cannot
erase the source initialization checkpoints or earlier numerical samples. -/
inductive Record where
  | initialization (observed : List (Float64Access.Observation Invocation)) (checkpoints : List Heap) (heap : Heap)
  | simulation (statuses : List Int) (events : List Invocation) (calls : List (CSRun.CallRecord Invocation)) (heap : Heap)
  | reset (events : List Invocation) (status : Value) (heap : Heap)

/-- This is sequencing of the existing raw relations, not another numerical
or C semantics. In particular reset has an arbitrary raw result value. -/
inductive Completed [CInterface] (program : Program Invocation) (p : Address) (access : Float64Buffers.Layout) :
    Heap → Plan → List Record → Heap → Prop where
  | finish : InitializationProtocol.Completed program p access heap actions observed after checkpoints →
      Completed program p access heap (.finish actions state) [.initialization observed checkpoints after] after
  | last : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      CSRun.Recorded program p exited cycle.simulation statuses events after calls →
      Completed program p access heap (.last cycle)
        [.initialization initial checkpoints exited, .simulation statuses events calls after] after
  | next : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      CSRun.Recorded program p exited cycle.simulation statuses events simulated calls →
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
      CSRun.Stopped program p exited cycle.simulation → Stopped program p access heap (.last cycle)
  | nextSimulation : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      CSRun.Stopped program p exited cycle.simulation → Stopped program p access heap (.next cycle following)
  | reset : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      CSRun.Recorded program p exited cycle.simulation statuses events simulated calls →
      (machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] simulated .done) (.wrong []) →
      Stopped program p access heap (.next cycle following)
  | later : InitializationProtocol.Completed program p access heap cycle.initialization initial exited checkpoints →
      CSRun.Recorded program p exited cycle.simulation statuses events simulated calls →
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

end Rumoca.FMI3.CSProtocol
end
