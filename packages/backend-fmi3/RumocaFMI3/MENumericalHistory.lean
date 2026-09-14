import RumocaFMI3.MEEnvironment
import RumocaFMI3.MENumericalMemory

noncomputable section
namespace Rumoca.FMI3.MENumericalHistory
open CTree CMemory

inductive Action where
  | control (action : MEHistory.Action)
  | setState (value : Binary64.Value)
  | getState
  | derivative

def Action.next (action : Action) (reference : ReferenceState) : ReferenceState :=
  match action with
  | .control command => { reference with control := command.next reference.control }
  | .setState value => { reference with state := ModelExchange.setContinuousState reference.state value }
  | _ => reference

def Action.Allowed (action : Action) (reference : ReferenceState) : Prop :=
  match action with
  | .control command => command.Allowed reference.control
  | .setState _ => reference.control.mode = .continuous
  | .getState => Reference.Allowed .getStates .me reference.control.mode
  | .derivative => Reference.Allowed .getDerivatives .me reference.control.mode

def Action.clock (action : Action) (clock : Time.Clock) : Time.Clock :=
  match action with | .control command => command.clock clock | _ => clock

def Action.prepare (action : Action) (heap : Heap) (buffer : Address) : Heap :=
  match action with
  | .setState value => StateProofs.written heap buffer (Binary64.toBits value).val
  | _ => heap

/-- This is an actual caller store, not an assumption about a future input. -/
def Action.Prepares (action : Action) (heap ready : Heap) (buffer : Address) : Prop :=
  match action with
  | .setState value => store heap buffer (.finite value) = some ready
  | _ => ready = heap

def Action.call (action : Action) (p : Address) (addresses : String → Address)
    (buffer : Address) : String × List Value :=
  match action with
  | .control command => command.call p addresses
  | .setState _ => ((StateCalls.signature true).name, StateCalls.arguments p buffer)
  | .getState => ((StateCalls.signature false).name, StateCalls.arguments p buffer)
  | .derivative => (DerivativeCalls.signature.name, DerivativeCalls.values (some p) (some buffer) 1)

def Action.after (model : Solve.FMI3Model source) (action : Action) (heap : Heap)
    (p : Address) (clock : Time.Clock) (reference : ReferenceState)
    (addresses : String → Address) (buffer : Address) : Heap :=
  match action with
  | .control command => command.heap heap p clock addresses
  | .setState value => StateProofs.written (action.prepare heap buffer)
      (StateProofs.stateAddress p) (Binary64.toBits value).val
  | .getState => StateProofs.written heap buffer (Binary64.toBits reference.state.x).val
  | .derivative => StateProofs.written heap buffer
      (Binary64.toBits (ModelExchange.derivative model.solve reference.state)).val

def Action.expected (model : Solve.FMI3Model source) (action : Action)
    (reference : ReferenceState) : Option Value :=
  match action with
  | .getState => some (.finite (ModelExchange.getContinuousState reference.state))
  | .derivative => some (.finite (ModelExchange.derivative model.solve reference.state))
  | _ => none

/-- Readback observes raw target memory, including a missing or non-finite
value. Finiteness and agreement with Solve are proved by the call certificate. -/
def Action.Observes (action : Action) (heap : Heap) (buffer : Address)
    (observed : Option Value) : Prop :=
  match action with
  | .getState | .derivative => observed = load heap buffer
  | _ => observed = none

/-- Expected control flags belong to the certificate, not the relation
describing arbitrary actual executions. -/
def Action.ControlOutputs (action : Action) (heap : Heap) (addresses : String → Address) : Prop :=
  match action with | .control command => command.Outputs heap addresses | _ => True

theorem Action.prepare_correct (action : Action) {clock : Time.Clock}
    (stored : Stored heap p clock reference addresses buffer) :
    action.Prepares heap (action.prepare heap buffer) buffer ∧
    Stored (action.prepare heap buffer) p clock reference addresses buffer ∧
    CReadOnly.Preserves heap (action.prepare heap buffer) := by
  cases action with
  | setState value => exact stored.prepare_buffer value
  | control _ | getState | derivative => exact ⟨rfl, stored, .refl heap⟩

theorem Stored.mode_loaded (stored : Stored heap p clock reference addresses buffer) :
    load heap (p.member "mode") = some (.integer reference.control.mode.code) := by
  cases mode : reference.control.mode <;> simp [load, stored.control.mode, mode, convert, Mode.code]

def Outside (p : Address) (addresses : String → Address) (buffer q : Address) : Prop :=
  MEHistory.Outside p addresses q ∧ q ≠ StateProofs.stateAddress p ∧ q ≠ buffer

theorem Action.frame (model : Solve.FMI3Model source) (action : Action)
    (heap : Heap) (p : Address) (clock : Time.Clock) (reference : ReferenceState)
    (addresses : String → Address) (buffer q : Address) (outside : Outside p addresses buffer q) :
    action.after model heap p clock reference addresses buffer q = heap q := by
  obtain ⟨control, state, output⟩ := outside
  cases action with
  | control command => exact MEHistory.action_frame command heap p q clock addresses control
  | setState value =>
    exact (StateProofs.written_frame _ _ q _ state).trans
      (StateProofs.written_frame heap buffer q _ output)
  | getState | derivative => exact StateProofs.written_frame heap buffer q _ output

/-- Every accepted mixed operation derives the input write, actual complete
FMI call, finite outputs, continued storage and read-only diagnostic frame. -/
theorem step [CInterface] (program : CCalls.Events.Program E)
    (quiet : MEEnvironment.Quiet model program)
    (stored : Stored heap p clock reference addresses buffer)
    (action : Action) (allowed : action.Allowed reference) :
    let ready := action.prepare heap buffer
    let after := action.after model heap p clock reference addresses buffer
    action.Prepares heap ready buffer ∧
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (action.call p addresses buffer).1 (action.call p addresses buffer).2 ready .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, after⟩) ∧
    Stored after p (action.clock clock) (action.next reference) addresses buffer ∧
    action.Observes after buffer (action.expected model reference) ∧
    action.ControlOutputs after addresses ∧
    CReadOnly.Preserves heap after ∧
    (∀ q, Outside p addresses buffer q → after q = heap q) := by
  have prepared := action.prepare_correct stored
  let ready := action.prepare heap buffer
  let after := action.after model heap p clock reference addresses buffer
  have result : (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (action.call p addresses buffer).1 (action.call p addresses buffer).2 ready .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, after⟩) ∧
      Stored after p (action.clock clock) (action.next reference) addresses buffer ∧
      action.Observes after buffer (action.expected model reference) ∧
      action.ControlOutputs after addresses := by
    cases action with
    | control command =>
      obtain ⟨called, controlAfter, outputs⟩ := MEHistory.step program quiet.control stored.control command allowed
      have stateFrame := MEHistory.action_frame command heap p (StateProofs.stateAddress p) clock addresses
        stored.control_frame.1
      have bufferFrame := MEHistory.action_frame command heap p buffer clock addresses stored.control_frame.2
      obtain ⟨old, cell⟩ := stored.bufferCell
      exact ⟨called, ⟨controlAfter, stateFrame.trans stored.stateCell,
        ⟨old, bufferFrame.trans cell⟩, stored.bufferOutside, stored.bufferSeparate⟩, rfl, outputs⟩
    | setState value =>
      change reference.control.mode = .continuous at allowed
      have modeLoaded : load ready (p.member "mode") = some (.integer 3) := by
        simpa only [allowed, Mode.code] using prepared.2.1.mode_loaded
      have input : load ready buffer = some (.finite value) := by
        simp [ready, Action.prepare, StateProofs.written, load, convert, Value.finite]
      exact ⟨(quiet.states ready).set p buffer reference.state value prepared.2.1.control.kind modeLoaded
          input prepared.2.1.stateCell,
        prepared.2.1.write_state value, rfl, True.intro⟩
    | getState =>
      obtain ⟨old, cell⟩ := stored.bufferCell
      refine ⟨(quiet.states heap).get p buffer reference.control.mode reference.state old stored.control.kind
        stored.mode_loaded allowed stored.control.modelStored cell, stored.write_buffer _, ?_, True.intro⟩
      simp [Action.Observes, Action.expected, after, Action.after, StateProofs.written,
        load, convert, Value.finite, ModelExchange.getContinuousState]
    | derivative =>
      obtain ⟨old, cell⟩ := stored.bufferCell
      refine ⟨(quiet.derivatives heap).get p buffer reference.control.mode reference.state old
        stored.control.kind stored.mode_loaded allowed cell, stored.write_buffer _, ?_, True.intro⟩
      simp [Action.Observes, Action.expected, after, Action.after, StateProofs.written, load, convert, Value.finite]
  exact ⟨prepared.1, result.1, result.2.1, result.2.2.1, result.2.2.2,
    prepared.2.2.trans (CCalls.Events.termination_preserves ((result.1 _).mpr rfl)),
    fun q outside => action.frame model heap p clock reference addresses buffer q outside⟩

end Rumoca.FMI3.MENumericalHistory
end

noncomputable section
namespace Rumoca.FMI3.MENumericalHistory
open CTree CMemory

theorem Action.Prepares.unique {action : Action} (first : action.Prepares heap ready buffer)
    (second : action.Prepares heap other buffer) : ready = other := by
  cases action <;> simp_all [Action.Prepares]

theorem Action.Observes.unique {action : Action} (first : action.Observes heap buffer a)
    (second : action.Observes heap buffer b) : a = b := by
  cases action <;> exact first.trans second.symm

inductive ReferenceTrace : ReferenceState → List Action → ReferenceState → Prop where
  | nil : ReferenceTrace reference [] reference
  | cons : action.Allowed reference → ReferenceTrace (action.next reference) rest final →
      ReferenceTrace reference (action :: rest) final

def observations (model : Solve.FMI3Model source) (reference : ReferenceState) :
    List Action → List (Option Value)
  | [] => []
  | action :: rest => action.expected model reference :: observations model (action.next reference) rest

/-- The actual target script records statuses, events and loaded outputs.
No source equation, reference transition or expected output is a premise. -/
structure Observation (E : Type) where
  events : List E
  status : Value
  value : Option Value

def Observation.ok (value : Option Value) : Observation E := ⟨[], .integer 0, value⟩

inductive Executed [CInterface] (program : CCalls.Events.Program E)
    (p : Address) (addresses : String → Address) (buffer : Address) :
    Heap → List Action → List (Observation E) → Heap → Prop where
  | nil : Executed program p addresses buffer heap [] [] heap
  | cons : action.Prepares heap ready buffer →
      (CCalls.Events.machine program).Behaves
        (.calling (action.call p addresses buffer).1 (action.call p addresses buffer).2 ready .done)
        (.terminates events ⟨status, after⟩) → action.Observes after buffer value →
      Executed program p addresses buffer after rest values final →
      Executed program p addresses buffer heap (action :: rest) (⟨events, status, value⟩ :: values) final

/-- A derived certificate retains all call behaviors, caller preparation,
output readback and every intermediate heap for an admitted script. -/
inductive Calls [CInterface] (program : CCalls.Events.Program E)
    (p : Address) (addresses : String → Address) (buffer : Address) :
    Heap → List Action → List (Option Value) → Heap → Prop where
  | nil : Calls program p addresses buffer heap [] [] heap
  | cons : action.Prepares heap ready buffer →
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (action.call p addresses buffer).1 (action.call p addresses buffer).2 ready .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, after⟩) →
      action.Observes after buffer value → action.ControlOutputs after addresses →
      Calls program p addresses buffer after rest values final →
      Calls program p addresses buffer heap (action :: rest) (value :: values) final

theorem trace [CInterface] (program : CCalls.Events.Program E)
    (quiet : MEEnvironment.Quiet model program)
    (stored : Stored heap p clock reference addresses buffer)
    (admitted : ReferenceTrace reference actions final) :
    ∃ after finalClock,
      Calls program p addresses buffer heap actions (observations model reference actions) after ∧
      Stored after p finalClock final addresses buffer ∧
      CReadOnly.Preserves heap after ∧
      (∀ q, Outside p addresses buffer q → after q = heap q) := by
  induction admitted generalizing heap clock with
  | nil => exact ⟨heap, clock, .nil, stored, .refl heap, fun _ _ => rfl⟩
  | cons accepted _ ih =>
    obtain ⟨prepared, called, storedAfter, output, controlOutputs, readonly, framed⟩ := step program quiet stored _ accepted
    obtain ⟨after, finalClock, following, storedFinal, readonlyRest, framedRest⟩ := ih storedAfter
    exact ⟨after, finalClock, .cons prepared called output controlOutputs following, storedFinal,
      readonly.trans readonlyRest, fun q outside => (framedRest q outside).trans (framed q outside)⟩

theorem Calls.executes [CInterface] {program : CCalls.Events.Program E}
    (certified : Calls program p addresses buffer heap actions values after) :
    Executed program p addresses buffer heap actions (values.map Observation.ok) after := by
  induction certified with
  | nil => exact .nil
  | cons prepared behavior output _ _ ih => exact .cons prepared ((behavior _).mpr rfl) output ih

/-- Agreement of every observed status, event and finite query output is a
consequence of actual execution, rather than a restriction on the host trace. -/
theorem Calls.determines [CInterface] {program : CCalls.Events.Program E}
    (certified : Calls program p addresses buffer heap actions values final)
    (executed : Executed program p addresses buffer heap actions observed after) :
    observed = values.map Observation.ok ∧ after = final := by
  induction executed generalizing values final with
  | nil => cases certified; exact ⟨rfl, rfl⟩
  | cons prepared called output _ ih =>
    cases certified with
    | cons certifiedPreparation behavior expected _ following =>
      have sameReady := Action.Prepares.unique certifiedPreparation prepared
      cases sameReady
      have returned := (behavior _).mp called
      cases returned
      have sameValue := Action.Observes.unique output expected
      obtain ⟨tail, finish⟩ := ih following
      exact ⟨by simp only [List.map_cons, Observation.ok, sameValue, tail], finish⟩

end Rumoca.FMI3.MENumericalHistory
end
