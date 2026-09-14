import RumocaFMI3.Float64RejectionExecution
import RumocaFMI3.CountRequests
import RumocaFMI3.NominalRequests

/-! Initialization is a protocol, not an indivisible reset/enter/exit macro.
Its reference transitions are independent of the target heaps and statuses.
The raw relation includes typed caller transfers and actual public C calls. -/
noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CMemory CCalls.Events

inductive Phase where
  | instantiated
  | initializing (args : Initialization.Arguments)
  | initialized (args : Initialization.Arguments)
  | failed

def Phase.mode (kind : Kind) : Phase → Mode
  | .instantiated => .instantiated
  | .initializing _ => .initialization
  | .initialized _ => nextMode .exitInitialization kind .initialization
  | .failed => .terminated

structure State where
  phase : Phase
  value : ModelExchange.State
  time : Binary64.Value

def State.reset : State := ⟨.instantiated, ⟨Binary64.positiveZero⟩, Binary64.positiveZero⟩

inductive Action where
  | access (request : Float64Access.Request)
  | reject (request : Float64Rejection.Request)
  | counts (request : CountAccess.Request)
  | nominals (request : NominalAccess.Request)
  | enter (args : Initialization.Arguments)
  | exit
  | reset

def Action.next (action : Action) (state : State) : State :=
  match action with
  | .access request => { state with value := request.next state.value }
  | .reject _ => { state with phase := .failed }
  | .counts request => if request.failed then { state with phase := .failed } else state
  | .nominals request => if request.failed then { state with phase := .failed } else state
  | .enter args => { state with phase := .initializing args, time := args.start }
  | .exit => match state.phase with
    | .initializing args => { state with phase := .initialized args }
    | _ => state
  | .reset => .reset

/-- Subsequent simulation is handled by the existing ME/CS histories; count
queries may also observe the instantiated or post-exit Event Mode. Reset can
start another epoch here. Before entry, variable reads concern start values,
not an evaluated equation system. -/
def Action.Allowed (action : Action) (kind : Kind) (state : State) : Prop :=
  match action with
  | .access request => match state.phase with
    | .instantiated => request.StartQuery
    | .initializing _ => request.Allowed kind .initialization
    | _ => False
  | .reject request => request.Condition kind (state.phase.mode kind)
  | .counts request => request.Allowed kind (state.phase.mode kind)
  | .nominals request => request.Allowed kind (state.phase.mode kind)
  | .enter args => state.phase = .instantiated ∧ args.Admissible
  | .exit => ∃ args, state.phase = .initializing args
  | .reset => True

inductive ReferenceTrace (kind : Kind) : State → List Action → State → Prop where
  | nil : ReferenceTrace kind state [] state
  | cons : action.Allowed kind state →
      ReferenceTrace kind (action.next state) rest final →
      ReferenceTrace kind state (action :: rest) final

def Action.call (action : Action) (p : Address) (buffers : Float64Buffers.Layout) : String × List Value :=
  match action with
  | .access request => request.call p buffers
  | .reject request => request.call p
  | .counts request => request.call p
  | .nominals request => request.call p
  | .enter args => (InitializationCalls.signature.name,
      InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args))
  | .exit => (InitializationExit.signature.name, InitializationExit.arguments (some p))
  | .reset => (Reset.signature.name, [.pointer (some p)])

def Action.hostRun (action : Action) (heap : Heap) (buffers : Float64Buffers.Layout) : Option Heap :=
  match action with
  | .access request => request.hostRun heap buffers
  | .reject request => request.hostRun heap
  | _ => some heap

/-- Failed output arguments have no numerical observation. -/
def Action.readback (action : Action) (heap : Heap) (buffers : Float64Buffers.Layout) : Nat → Option Value :=
  match action with
  | .access request => request.readback heap buffers
  | .counts request => request.readback heap
  | .nominals request => request.readback heap
  | _ => fun _ => none

def Action.Observed (action : Action) (model : Solve.FMI3Model source) (state : State)
    (observed : Float64Access.Observation Invocation) : Prop :=
  match action with
  | .access request => observed = .ok (request.expected model state.value state.time)
  | .reject _ => observed.status = .integer 3 ∧ observed.values = fun _ => none
  | .counts request => if request.failed then
      observed.status = .integer 3 ∧ observed.values = fun _ => none
    else observed = .ok (request.expected model)
  | .nominals request => if request.failed then
      observed.status = .integer 3 ∧ observed.values = fun _ => none
    else observed = .ok (request.expected model)
  | _ => observed = .ok (fun _ => none)

/-- An exit checkpoint keeps the actual heap. Source initialization is proved
about this heap, even if a later reset chooses a different initial value. -/
def Action.checkpoints (action : Action) (after : Heap) : List Heap :=
  match action with
  | .exit => [after]
  | _ => []

def Action.Behaves [CInterface] (action : Action) (program : Program Invocation)
    (heap : Heap) (p : Address) (buffers : Float64Buffers.Layout)
    (behavior : Transition.Events.Observation Invocation CBody.Result) : Prop :=
  ∃ ready, action.hostRun heap buffers = some ready ∧
    (machine program).Behaves (.calling (action.call p buffers).1 (action.call p buffers).2 ready .done) behavior

inductive Completed [CInterface] (program : Program Invocation) (p : Address) (buffers : Float64Buffers.Layout) :
    Heap → List Action → List (Float64Access.Observation Invocation) → Heap → List Heap → Prop where
  | nil : Completed program p buffers heap [] [] heap []
  | cons : action.Behaves program heap p buffers (.terminates events ⟨status, middle⟩) →
      Completed program p buffers middle rest observed after checkpoints →
      Completed program p buffers heap (action :: rest)
        (⟨events, status, action.readback middle buffers⟩ :: observed) after
        (action.checkpoints middle ++ checkpoints)

end Rumoca.FMI3.InitializationProtocol
end
