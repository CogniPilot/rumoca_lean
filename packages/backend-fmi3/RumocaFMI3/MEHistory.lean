import RumocaFMI3.EventEntryHistory
import RumocaFMI3.CompletedHistory
import RumocaFMI3.DiscreteHistory
import RumocaFMI3.DiscreteEvaluationContract

noncomputable section
namespace Rumoca.FMI3.MEHistory
open CTree CMemory CBody EventEntry

/-! Quiescent ME time, mode, discrete-update and completion histories. The
reference protocol requires a completed event iteration before continuous entry.
Caller buffers are retained across the whole trace, allowing compatible aliases.
State setters, derivative queries, importer integration, failures and concurrent
callers require separate composition before a whole-ME simulation theorem. -/

inductive Action where
  | setTime (time : Binary64.Value)
  | enter (entry : EventEntry.Entry)
  | updateDiscrete
  | evaluateDiscrete
  | completed (noSetState : Bool)

structure ReferenceState where
  mode : Mode
  history : Time.History
  eventReady : Bool

def ReferenceState.initial (start : Binary64.Value) (stop : Option Binary64.Value) : ReferenceState :=
  ⟨.event, .initial start stop, false⟩

def Action.next (action : Action) (state : ReferenceState) : ReferenceState :=
  match action with
  | .setTime time => { state with history := state.history.setTime time }
  | .enter entry => ⟨entry.after, afterHistory entry state.history, false⟩
  | .updateDiscrete => { state with eventReady := true }
  | .evaluateDiscrete => state
  | .completed _ => { state with history := state.history.completed }

def Action.Allowed (action : Action) (state : ReferenceState) : Prop :=
  match action with
  | .setTime time => Reference.Allowed .setTime .me state.mode ∧ state.history.window.Admissible time
  | .enter entry => Reference.Allowed entry.command .me state.mode ∧
      (entry = .continuous → state.eventReady = true)
  | .updateDiscrete => Reference.Allowed .updateDiscrete .me state.mode
  | .evaluateDiscrete => Reference.Allowed .evaluateDiscrete .me state.mode
  | .completed _ => Reference.Allowed .completedStep .me state.mode

def Action.call (action : Action) (p : Address) (addresses : String → Address) : String × List Value :=
  match action with
  | .setTime time => (TimeCalls.signature.name, TimeCalls.arguments (some p) (Binary64.toBits time).val)
  | .enter entry => ((signature entry).name, [.pointer (some p)])
  | .updateDiscrete => (DiscreteCalls.signature.name, DiscreteCalls.arguments (some p) (fun name => some (addresses name)))
  | .evaluateDiscrete => (DiscreteEvaluation.signature.name, DiscreteEvaluation.arguments (some p))
  | .completed flag => (CompletedCalls.signature.name, CompletedCalls.arguments (some p)
      (some (addresses "discreteStatesNeedUpdate")) (some (addresses "terminateSimulation")) flag)

def Action.clock (action : Action) (clock : Time.Clock) : Time.Clock :=
  match action with
  | .setTime time => clock.setTime time
  | .enter entry => afterClock entry clock
  | .updateDiscrete => clock
  | .evaluateDiscrete => clock
  | .completed _ => clock.completed

def Action.heap (action : Action) (heap : Heap) (p : Address) (clock : Time.Clock)
    (addresses : String → Address) : Heap :=
  match action with
  | .setTime time => StateProofs.written heap (p.member "time") (Binary64.toBits time).val
  | .enter entry => afterHeap entry heap p clock
  | .updateDiscrete => COutputAssignments.after heap (DiscreteCalls.outputs addresses)
  | .evaluateDiscrete => heap
  | .completed _ => HistoryBodies.completedHeap heap p
      (addresses "discreteStatesNeedUpdate") (addresses "terminateSimulation") clock

/-- Output values are consequences of the calls, including the false
iteration flag which justifies the reference protocol's ready transition. -/
def Action.Outputs (action : Action) (heap : Heap) (addresses : String → Address) : Prop :=
  match action with
  | .updateDiscrete => ∀ layout ∈ DiscreteCalls.layouts,
      load heap (addresses layout.1) = some (DiscreteCalls.zeroValue layout.2)
  | .completed _ => load heap (addresses "discreteStatesNeedUpdate") = some (boolean false) ∧
      load heap (addresses "terminateSimulation") = some (boolean false)
  | _ => True

def Buffers (heap : Heap) (addresses : String → Address) : Prop :=
  ∀ layout ∈ DiscreteCalls.layouts, COutputAssignments.Writable heap (DiscreteCalls.output addresses layout)

def Buffers.Outside (p : Address) (addresses : String → Address) : Prop :=
  ∀ name ∈ DiscreteCalls.names, (addresses name).block ≠ p.block

theorem Buffers.writable (buffers : Buffers heap addresses) :
    ∀ entry ∈ DiscreteCalls.outputs addresses, COutputAssignments.Writable heap entry := by
  intro entry member
  change entry ∈ DiscreteCalls.layouts.map (DiscreteCalls.output addresses) at member
  obtain ⟨layout, declared, rfl⟩ := List.mem_map.mp member
  exact buffers layout declared

theorem Buffers.transport (buffers : Buffers heap addresses)
    (same : ∀ layout ∈ DiscreteCalls.layouts, after (addresses layout.1) = heap (addresses layout.1)) :
    Buffers after addresses := by
  intro layout member
  obtain ⟨old, cell⟩ := buffers layout member
  exact ⟨old, (same layout member).trans cell⟩

theorem Buffers.Outside.field (outside : Buffers.Outside p addresses)
    (layout : String × CType) (member : layout ∈ DiscreteCalls.layouts) (name : String) :
    addresses layout.1 ≠ p.member name := by
  intro same
  have blockSame := congrArg Address.block same
  exact outside layout.1 (List.mem_map.mpr ⟨layout, member, rfl⟩) (by simpa using blockSame)

theorem Buffers.zero (buffers : Buffers heap addresses) (name : String)
    (member : (name, CType.boolean) ∈ DiscreteCalls.layouts) :
    Buffers (HistoryBodies.zero heap (addresses name)) addresses := by
  intro layout declared
  have kept := COutputAssignments.writable_preserved (buffers (name, .boolean) member) (buffers layout declared)
  simpa only [COutputAssignments.write, DiscreteCalls.output, DiscreteCalls.zeroValue,
    HistoryBodies.zero] using kept

theorem Buffers.completed (buffers : Buffers heap addresses) (outside : Buffers.Outside p addresses)
    (clock : Time.Clock) :
    Buffers (HistoryBodies.completedHeap heap p (addresses "discreteStatesNeedUpdate")
      (addresses "terminateSimulation") clock) addresses := by
  have ready := (buffers.zero "discreteStatesNeedUpdate" (by decide +kernel)).zero
    "terminateSimulation" (by decide +kernel)
  apply ready.transport
  intro layout member
  exact HistoryProofs.completed_frame _ p (addresses layout.1) clock
    (outside.field layout member "lastCompleted") (outside.field layout member "timeMin")

theorem Buffers.discrete (buffers : Buffers heap addresses) :
    Buffers (COutputAssignments.after heap (DiscreteCalls.outputs addresses)) addresses := by
  intro layout member
  exact ⟨some (DiscreteCalls.output addresses layout).value,
    COutputAssignments.outputs_stored (DiscreteCalls.outputs_compatible buffers.writable)
      _ (List.mem_map.mpr ⟨layout, member, rfl⟩)⟩

structure Stored (heap : Heap) (p : Address) (clock : Time.Clock)
    (reference : ReferenceState) (model : ModelExchange.State) (addresses : String → Address) : Prop where
  kind : load heap (p.member "kind") = some (.integer 0)
  mode : heap (p.member "mode") = some ⟨.int32, true, some (.integer reference.mode.code)⟩
  clockStored : HistoryProofs.Stored heap p clock
  history : Time.Represents reference.history clock
  modelStored : StateProofs.Represents heap p model
  stopDefined : load heap (p.member "stopDefined") = some (boolean reference.history.window.stopTime.isSome)
  stopValue : ∀ stop, reference.history.window.stopTime = some stop → load heap (p.member "stop") = some (.finite stop)
  buffers : Buffers heap addresses
  outside : Buffers.Outside p addresses

structure Quiet [interface : CInterface] (program : CCalls.Events.Program E) : Prop where
  time : TimeCalls.QuietContract program
  entry : ∀ entry, EventEntry.QuietContract entry program
  completed : CompletedCalls.QuietContract program
  discrete : DiscreteCalls.QuietContract program
  evaluation : DiscreteEvaluation.QuietContract program

theorem step [interface : CInterface] (program : CCalls.Events.Program E) (quiet : Quiet program)
    (stored : Stored heap p clock reference model addresses) (action : Action) (accepted : action.Allowed reference) :
    let after := action.heap heap p clock addresses
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (action.call p addresses).1 (action.call p addresses).2 heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, after⟩) ∧
    Stored after p (action.clock clock) (action.next reference) model addresses ∧
    action.Outputs after addresses := by
  cases action with
  | setTime time =>
    obtain ⟨⟨_, mode⟩, admissible⟩ := accepted
    have modeCell : heap (p.member "mode") = some ⟨.int32, true, some (.integer 3)⟩ := by
      simpa only [mode, Mode.code] using stored.mode
    have modeLoaded : load heap (p.member "mode") = some (.integer 3) := by
      simp [load, modeCell, convert]
    obtain ⟨called, clockAfter, historyAfter, modelAfter, boundsAfter, framed⟩ :=
      TimeCalls.history_call program quiet.time heap p clock reference.history time model
        stored.kind modeLoaded stored.clockStored stored.history stored.modelStored
        stored.stopDefined stored.stopValue admissible
    refine ⟨called, ?_, True.intro⟩
    constructor
    · simpa only [Action.heap, load, framed (p.member "kind") (by simp)] using stored.kind
    · simpa only [Action.heap, Action.next, framed (p.member "mode") (by simp)] using stored.mode
    · exact clockAfter
    · exact historyAfter
    · exact modelAfter
    · exact boundsAfter.stopDefined
    · exact boundsAfter.stopValue
    · exact stored.buffers.transport (fun layout member => framed _ (stored.outside.field layout member "time"))
    · exact stored.outside
  | enter entry =>
    have mode := ((EventEntry.allowed entry .me reference.mode).mp accepted.1).2
    have modeCell : heap (p.member "mode") = some ⟨.int32, true, some (.integer entry.before.code)⟩ := by
      simpa only [mode] using stored.mode
    obtain ⟨called, clockAfter, historyAfter, modelAfter, modeAfter, boundsAfter, framed⟩ :=
      EventEntry.history_call entry program (quiet.entry entry) heap p clock reference.history model
        stored.kind modeCell stored.clockStored stored.history stored.modelStored
        stored.stopDefined stored.stopValue
    refine ⟨called, ?_, True.intro⟩
    constructor
    · simpa only [Action.heap, load, framed (p.member "kind") (by simp) (by intro _; simp)] using stored.kind
    · exact modeAfter
    · exact clockAfter
    · exact historyAfter
    · exact modelAfter
    · exact boundsAfter.stopDefined
    · exact boundsAfter.stopValue
    · exact stored.buffers.transport (fun layout member => framed _ (stored.outside.field layout member "mode")
        (fun _ => ⟨stored.outside.field layout member "eventTime", stored.outside.field layout member "timeMin"⟩))
    · exact stored.outside
  | evaluateDiscrete =>
    have modeLoaded : load heap (p.member "mode") = some (.integer reference.mode.code) := by
      cases mode : reference.mode <;> simp [load, stored.mode, mode, convert, Mode.code]
    exact ⟨quiet.evaluation.successful heap p .me reference.mode stored.kind modeLoaded accepted,
      stored, True.intro⟩
  | updateDiscrete =>
    have mode : reference.mode = .event := accepted.2
    have modeCell : heap (p.member "mode") = some ⟨.int32, true, some (.integer 2)⟩ := by
      simpa only [mode, Mode.code] using stored.mode
    obtain ⟨called, clockAfter, historyAfter, modelAfter, modeAfter, boundsAfter, outputs, framed⟩ :=
      DiscreteCalls.history_call program quiet.discrete heap p addresses clock reference.history model
        stored.kind modeCell stored.clockStored stored.history stored.modelStored stored.stopDefined
        stored.stopValue stored.buffers.writable stored.outside
    refine ⟨called, ?_, outputs⟩
    constructor
    · simpa only [Action.heap, load, framed (p.member "kind") rfl] using stored.kind
    · simpa only [Action.next, mode, Mode.code] using modeAfter
    · exact clockAfter
    · exact historyAfter
    · exact modelAfter
    · exact boundsAfter.stopDefined
    · exact boundsAfter.stopValue
    · exact stored.buffers.discrete
    · exact stored.outside
  | completed flag =>
    have mode : reference.mode = .continuous := accepted.2
    have modeCell : heap (p.member "mode") = some ⟨.int32, true, some (.integer 3)⟩ := by
      simpa only [mode, Mode.code] using stored.mode
    have modeLoaded : load heap (p.member "mode") = some (.integer 3) := by simp [load, modeCell, convert]
    have eventOutside := stored.outside "discreteStatesNeedUpdate" (by decide +kernel)
    have terminateOutside := stored.outside "terminateSimulation" (by decide +kernel)
    obtain ⟨called, clockAfter, historyAfter, modelAfter, _, eventAfter, terminateAfter, boundsAfter, framed⟩ :=
      CompletedCalls.history_call program quiet.completed heap p (addresses "discreteStatesNeedUpdate")
        (addresses "terminateSimulation") flag clock reference.history model stored.kind modeLoaded
        stored.clockStored stored.history stored.modelStored stored.stopDefined stored.stopValue
        (stored.buffers ("discreteStatesNeedUpdate", .boolean) (by decide +kernel))
        (stored.buffers ("terminateSimulation", .boolean) (by decide +kernel)) eventOutside terminateOutside
    refine ⟨called, ?_, eventAfter, terminateAfter⟩
    constructor
    · simpa only [Action.heap, load, framed (p.member "kind") (by simp) (by simp)
        (HistoryBodies.field_ne_output p _ _ eventOutside) (HistoryBodies.field_ne_output p _ _ terminateOutside)] using stored.kind
    · simpa only [Action.heap, Action.next, framed (p.member "mode") (by simp) (by simp)
        (HistoryBodies.field_ne_output p _ _ eventOutside) (HistoryBodies.field_ne_output p _ _ terminateOutside)] using stored.mode
    · exact clockAfter
    · exact historyAfter
    · exact modelAfter
    · exact boundsAfter.stopDefined
    · exact boundsAfter.stopValue
    · exact stored.buffers.completed stored.outside clock
    · exact stored.outside

inductive ReferenceTrace : ReferenceState → List Action → ReferenceState → Prop where
  | nil : ReferenceTrace reference [] reference
  | cons : action.Allowed reference → ReferenceTrace (action.next reference) rest final →
      ReferenceTrace reference (action :: rest) final

/-- Every call retains all its behaviors, concrete outputs and intermediate
heap; successful target executions are derived rather than given as premises. -/
inductive Calls [interface : CInterface] (program : CCalls.Events.Program E)
    (p : Address) (addresses : String → Address) : Heap → List Action → Heap → Prop where
  | nil : Calls program p addresses heap [] heap
  | cons : (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (action.call p addresses).1 (action.call p addresses).2 heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, after⟩) → action.Outputs after addresses →
      Calls program p addresses after rest final → Calls program p addresses heap (action :: rest) final

theorem trace [interface : CInterface] (program : CCalls.Events.Program E) (quiet : Quiet program)
    (stored : Stored heap p clock reference model addresses) (admitted : ReferenceTrace reference actions final) :
    ∃ after finalClock, Calls program p addresses heap actions after ∧
      Stored after p finalClock final model addresses := by
  induction admitted generalizing heap clock with
  | nil => exact ⟨heap, clock, .nil, stored⟩
  | cons accepted _ ih =>
    obtain ⟨called, storedAfter, outputs⟩ := step program quiet stored _ accepted
    obtain ⟨after, finalClock, calledRest, storedFinal⟩ := ih storedAfter
    exact ⟨after, finalClock, .cons called outputs calledRest, storedFinal⟩

theorem continuous_requires_iteration
    (accepted : Action.Allowed (.enter .continuous) reference) : reference.eventReady = true :=
  accepted.2 rfl

theorem initial_requires_iteration (start : Binary64.Value) (stop : Option Binary64.Value) :
    ¬ Action.Allowed (.enter .continuous) (ReferenceState.initial start stop) := by
  intro accepted
  have ready := continuous_requires_iteration accepted
  simp [ReferenceState.initial] at ready

def Outside (p : Address) (addresses : String → Address) (query : Address) : Prop :=
  query ≠ p.member "time" ∧ query ≠ p.member "mode" ∧
    query ≠ p.member "eventTime" ∧ query ≠ p.member "timeMin" ∧
    query ≠ p.member "lastCompleted" ∧ ∀ name ∈ DiscreteCalls.names, query ≠ addresses name

theorem action_frame (action : Action) (heap : Heap) (p query : Address) (clock : Time.Clock)
    (addresses : String → Address) (outside : Outside p addresses query) :
    action.heap heap p clock addresses query = heap query := by
  obtain ⟨time, mode, event, minimum, completed, outputs⟩ := outside
  cases action with
  | setTime _ => exact TimeCalls.frame heap p query _ time
  | enter entry => exact EventEntry.frame entry heap p query clock mode (fun _ => ⟨event, minimum⟩)
  | updateDiscrete => exact DiscreteCalls.frame heap addresses query outputs
  | evaluateDiscrete => rfl
  | completed _ =>
    exact HistoryBodies.completed_frame heap p _ _ query clock completed minimum
      (outputs "discreteStatesNeedUpdate" (by decide +kernel)) (outputs "terminateSimulation" (by decide +kernel))

theorem trace_frame [interface : CInterface] (program : CCalls.Events.Program E) (quiet : Quiet program)
    (stored : Stored heap p clock reference model addresses) (admitted : ReferenceTrace reference actions final) :
    ∃ after finalClock, Calls program p addresses heap actions after ∧
      Stored after p finalClock final model addresses ∧
      (∀ query, Outside p addresses query → after query = heap query) := by
  induction admitted generalizing heap clock with
  | nil => exact ⟨heap, clock, .nil, stored, fun _ _ => rfl⟩
  | cons accepted _ ih =>
    obtain ⟨called, storedAfter, outputs⟩ := step program quiet stored _ accepted
    obtain ⟨after, finalClock, calledRest, storedFinal, framed⟩ := ih storedAfter
    refine ⟨after, finalClock, .cons called outputs calledRest, storedFinal, ?_⟩
    intro query outside
    exact (framed query outside).trans (action_frame _ heap p query clock addresses outside)

/-- Evaluating the discrete equations does not signal a converged event
iteration; only UpdateDiscreteStates supplies that protocol observation. -/
theorem evaluation_preserves_iteration (reference : ReferenceState) :
    (Action.evaluateDiscrete.next reference).eventReady = reference.eventReady := rfl

theorem initial_evaluation_still_requires_iteration
    (start : Binary64.Value) (stop : Option Binary64.Value) :
    ¬ Action.Allowed (.enter .continuous)
      (Action.evaluateDiscrete.next (ReferenceState.initial start stop)) :=
  initial_requires_iteration start stop

end Rumoca.FMI3.MEHistory
