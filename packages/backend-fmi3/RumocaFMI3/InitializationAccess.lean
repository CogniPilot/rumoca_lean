import RumocaFMI3.Float64History
import RumocaFMI3.InitializationRuntime

noncomputable section
namespace Rumoca.FMI3.InitializationAccess
open CMemory Float64Buffers Float64Access

theorem start_allowed (request : Request) (kind : Kind) (start : request.StartQuery) :
    request.Allowed kind .instantiated := by
  cases request with
  | get shape references => exact ⟨trivial, fun i hi => by rw [start i hi]; decide⟩
  | set _ => exact Or.inl rfl

theorem entry_storage (stored : InitializationCalls.EntryStorage before p)
    (fields : ∀ name, after (p.member name) = before (p.member name)) :
    InitializationCalls.EntryStorage after p := by
  obtain ⟨clock, mode, ⟨oldStop, stop⟩, ⟨oldDefined, defined⟩⟩ := stored
  exact ⟨⟨by simpa only [fields] using clock.time, by simpa only [fields] using clock.minimum,
    by simpa only [fields] using clock.eventTime, by simpa only [fields] using clock.lastCompleted⟩,
    (fields "mode").trans mode, ⟨oldStop, (fields "stop").trans stop⟩,
    ⟨oldDefined, (fields "stopDefined").trans defined⟩⟩

theorem entered_instance (stored : Instance heap p kind .instantiated state time)
    (args : Initialization.Arguments) :
    Instance (InitializationEntry.finalHeap heap p args) p kind .initialization state args.start := by
  have stateFrame := InitializationEntry.frame heap p (StateProofs.stateAddress p) args
    (HistoryBodies.state_ne_field p "time") (HistoryBodies.state_ne_field p "timeMin")
    (HistoryBodies.state_ne_field p "eventTime") (HistoryBodies.state_ne_field p "lastCompleted")
    (HistoryBodies.state_ne_field p "stop") (HistoryBodies.state_ne_field p "stopDefined")
    (HistoryBodies.state_ne_field p "mode")
  refine ⟨(InitializationCalls.entered_kind heap p args).trans stored.kind,
    InitializationCalls.entered_mode heap p args, stateFrame.trans stored.state, ?_⟩
  simp [load, (InitializationCalls.stored heap p args).time, convert, Value.finite, Time.Clock.initial, HistoryProofs.cell]

theorem entered_buffers (stored : Stored heap buffers) (separate : buffers.Separate p)
    (args : Initialization.Arguments) : Stored (InitializationEntry.finalHeap heap p args) buffers := by
  have frame : ∀ q, q.block ≠ p.block → InitializationEntry.finalHeap heap p args q = heap q := by
    intro q different
    have fields : ∀ name, q ≠ p.member name := fun _ => different_blocks _ _ different
    exact InitializationEntry.frame heap p q args (fields _) (fields _) (fields _) (fields _)
      (fields _) (fields _) (fields _)
  constructor
  · intro i hi
    obtain ⟨old, cell⟩ := stored.references i hi
    exact ⟨old, (frame (buffers.references.index i) separate.references).trans cell⟩
  · intro i hi
    obtain ⟨old, cell⟩ := stored.values i hi
    exact ⟨old, (frame (buffers.values.index i) separate.values).trans cell⟩

theorem exited_instance (stored : Instance heap p kind .initialization state time) :
    Instance (InitializationBodies.exitHeap heap p kind) p kind
      (nextMode .exitInitialization kind .initialization) state time := by
  have fields : ∀ name, name ≠ "mode" →
      InitializationBodies.exitHeap heap p kind (p.member name) = heap (p.member name) :=
    fun name other => InitializationBodies.exit_frame heap p _ kind (by simpa using other)
  refine ⟨by simpa only [load, fields "kind" (by decide)] using stored.kind,
    by simp [InitializationBodies.exitHeap],
    (InitializationBodies.exit_frame heap p _ kind (HistoryBodies.state_ne_field p "mode")).trans stored.state,
    by simpa only [load, fields "time" (by decide)] using stored.time⟩

theorem exited_buffers (stored : Stored heap buffers) (separate : buffers.Separate p) (kind : Kind) :
    Stored (InitializationBodies.exitHeap heap p kind) buffers := by
  constructor
  · intro i hi
    obtain ⟨old, cell⟩ := stored.references i hi
    exact ⟨old, (InitializationBodies.exit_frame heap p (buffers.references.index i) kind
      (different_blocks _ _ separate.references)).trans cell⟩
  · intro i hi
    obtain ⟨old, cell⟩ := stored.values i hi
    exact ⟨old, (InitializationBodies.exit_frame heap p (buffers.values.index i) kind
      (different_blocks _ _ separate.values)).trans cell⟩

def writtenFields : List String := ["time", "timeMin", "eventTime", "lastCompleted", "stop", "stopDefined", "mode"]

def OutsideInitialization (p : Address) (buffers : Layout) (q : Address) : Prop :=
  Outside buffers q ∧ q ≠ StateProofs.stateAddress p ∧ ∀ name ∈ writtenFields, q ≠ p.member name

/-- The heaps are outputs of the construction, not host-supplied premises.
Readback before entry concerns start values; queries during initialization use
the equation environment at the supplied start time. -/
structure Certificate [CInterface] (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (p : Address) (buffers : Layout) (args : Initialization.Arguments) (kind : Kind)
    (state : ModelExchange.State) (time : Binary64.Value) (heap : Heap)
    (before during : List Request) (beforeEntry atExit : Heap) : Prop where
  beforeCalls : Calls program p buffers heap before (expected model time before state) beforeEntry
  enterCall : ∀ behavior, (CCalls.Events.machine program).Behaves
    (.calling InitializationCalls.signature.name
      (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) beforeEntry .done) behavior ↔
    behavior = .terminates [] ⟨.integer 0, InitializationEntry.finalHeap beforeEntry p args⟩
  duringCalls : Calls program p buffers (InitializationEntry.finalHeap beforeEntry p args) during
    (expected model args.start during (finalState before state)) atExit
  exitCall : ∀ behavior, (CCalls.Events.machine program).Behaves
    (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) atExit .done) behavior ↔
    behavior = .terminates [] ⟨.integer 0, InitializationBodies.exitHeap atExit p kind⟩
  instanceStored : Instance (InitializationBodies.exitHeap atExit p kind) p kind
    (nextMode .exitInitialization kind .initialization) (finalState during (finalState before state)) args.start
  buffersStored : Stored (InitializationBodies.exitHeap atExit p kind) buffers
  clockStored : HistoryProofs.Stored (InitializationBodies.exitHeap atExit p kind) p (Time.Clock.initial args.start)
  readonly : CReadOnly.Preserves heap (InitializationBodies.exitHeap atExit p kind)
  frame : ∀ q, OutsideInitialization p buffers q → InitializationBodies.exitHeap atExit p kind q = heap q
  beforeFields : ∀ name, beforeEntry (p.member name) = heap (p.member name)
  atExitFields : ∀ name, atExit (p.member name) = InitializationEntry.finalHeap beforeEntry p args (p.member name)

theorem initialization_history [CInterface] (program : CCalls.Events.Program E)
    (initialization : InitializationCalls.QuietExecutionContract program)
    (get : ∀ heap, Float64Calls.QuietExecutionContract model program heap)
    (set : ∀ heap, Float64Set.QuietExecutionContract program heap)
    (stored : Instance heap p kind .instantiated state time)
    (entryStored : InitializationCalls.EntryStorage heap p)
    (buffersStored : Stored heap buffers) (separate : buffers.Separate p)
    (args : Initialization.Arguments) (admissible : args.Admissible)
    (before during : List Request)
    (beforeFits : ∀ request ∈ before, request.Fits buffers)
    (beforeAllowed : ∀ request ∈ before, request.StartQuery)
    (duringFits : ∀ request ∈ during, request.Fits buffers)
    (duringAllowed : ∀ request ∈ during, request.Allowed kind .initialization) :
    ∃ beforeEntry atExit, Certificate model program p buffers args kind state time heap before during beforeEntry atExit := by
  obtain ⟨beforeEntry, beforeCalls, beforeInstance, beforeBuffers, _, beforeReadonly, beforeFrame⟩ :=
    trace program get set before stored buffersStored separate beforeFits
      (fun request member => start_allowed request kind (beforeAllowed request member))
  have beforeFields : ∀ name, beforeEntry (p.member name) = heap (p.member name) :=
    fun name => beforeFrame _ (Ne.symm (HistoryBodies.state_ne_field p name)) (instance_outside separate rfl)
  have enterCall := initialization.enter beforeEntry p args kind admissible
    (entry_storage entryStored beforeFields) beforeInstance.kind
  have enterReadonly := CCalls.Events.termination_preserves ((enterCall _).mpr rfl)
  obtain ⟨atExit, duringCalls, duringInstance, duringBuffers, _, duringReadonly, duringFrame⟩ :=
    trace program get set during (entered_instance beforeInstance args) (entered_buffers beforeBuffers separate args)
      separate duringFits duringAllowed
  have exitCall := initialization.exit atExit p kind duringInstance.kind duringInstance.mode
  have exitReadonly := CCalls.Events.termination_preserves ((exitCall _).mpr rfl)
  have duringFields : ∀ name, atExit (p.member name) = InitializationEntry.finalHeap beforeEntry p args (p.member name) :=
    fun name => duringFrame _ (Ne.symm (HistoryBodies.state_ne_field p name)) (instance_outside separate rfl)
  have clock := InitializationCalls.stored beforeEntry p args
  have currentClock : HistoryProofs.Stored atExit p (Time.Clock.initial args.start) :=
    ⟨(duringFields "time").trans clock.time, (duringFields "timeMin").trans clock.minimum,
      (duringFields "eventTime").trans clock.eventTime, (duringFields "lastCompleted").trans clock.lastCompleted⟩
  refine ⟨beforeEntry, atExit, beforeCalls, enterCall, duringCalls, exitCall,
    exited_instance duringInstance, exited_buffers duringBuffers separate kind,
    InitializationBodies.exit_history currentClock kind,
    beforeReadonly.trans (enterReadonly.trans (duringReadonly.trans exitReadonly)), ?_, beforeFields, duringFields⟩
  intro q ⟨outside, notState, fields⟩
  exact (InitializationBodies.exit_frame atExit p q kind (fields "mode" (by simp [writtenFields]))).trans
    ((duringFrame q notState outside).trans
      ((InitializationEntry.frame beforeEntry p q args
        (fields "time" (by simp [writtenFields])) (fields "timeMin" (by simp [writtenFields]))
        (fields "eventTime" (by simp [writtenFields])) (fields "lastCompleted" (by simp [writtenFields]))
        (fields "stop" (by simp [writtenFields])) (fields "stopDefined" (by simp [writtenFields]))
        (fields "mode" (by simp [writtenFields]))).trans (beforeFrame q notState outside)))

end Rumoca.FMI3.InitializationAccess
end

noncomputable section
namespace Rumoca.FMI3.InitializationAccess
open CMemory Float64Buffers Float64Access

structure Observation (E : Type) where
  before : List (Float64Access.Observation E)
  enterEvents : List E
  enterStatus : Value
  during : List (Float64Access.Observation E)
  exitEvents : List E
  exitStatus : Value

def expectedObservation (model : Solve.FMI3Model source) (state : ModelExchange.State)
    (time : Binary64.Value) (args : Initialization.Arguments) (before during : List Request) : Observation E :=
  ⟨(expected model time before state).map Float64Access.Observation.ok, [], .integer 0,
    (expected model args.start during (finalState before state)).map Float64Access.Observation.ok, [], .integer 0⟩

def Executed [CInterface] (program : CCalls.Events.Program E) (p : Address) (buffers : Layout)
    (args : Initialization.Arguments) (heap : Heap) (before during : List Request)
    (observation : Observation E) (after : Heap) : Prop :=
  ∃ beforeEntry entered atExit,
    Float64Access.Executed program p buffers heap before observation.before beforeEntry ∧
    (CCalls.Events.machine program).Behaves
      (.calling InitializationCalls.signature.name
        (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) beforeEntry .done)
      (.terminates observation.enterEvents ⟨observation.enterStatus, entered⟩) ∧
    Float64Access.Executed program p buffers entered during observation.during atExit ∧
    (CCalls.Events.machine program).Behaves
      (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) atExit .done)
      (.terminates observation.exitEvents ⟨observation.exitStatus, after⟩)

theorem Certificate.executes [CInterface] {program : CCalls.Events.Program E}
    (certified : Certificate model program p buffers args kind state time heap before during beforeEntry atExit) :
    Executed program p buffers args heap before during
      (expectedObservation model state time args before during) (InitializationBodies.exitHeap atExit p kind) :=
  ⟨beforeEntry, InitializationEntry.finalHeap beforeEntry p args, atExit,
    certified.beforeCalls.executes, (certified.enterCall _).mpr rfl,
    certified.duringCalls.executes, (certified.exitCall _).mpr rfl⟩

theorem Certificate.determines [CInterface] {program : CCalls.Events.Program E}
    (certified : Certificate model program p buffers args kind state time heap before during beforeEntry atExit)
    (executed : Executed program p buffers args heap before during observation after) :
    observation = expectedObservation model state time args before during ∧
      after = InitializationBodies.exitHeap atExit p kind := by
  obtain ⟨actualBefore, actualEntered, actualExit, prefixCalls, enterCall, duringCalls, exitCall⟩ := executed
  obtain ⟨beforeObserved, sameBefore⟩ := certified.beforeCalls.determines prefixCalls
  subst actualBefore
  have enterResult := (certified.enterCall _).mp enterCall
  have enterEqual : observation.enterEvents = [] ∧ observation.enterStatus = .integer 0 ∧
      actualEntered = InitializationEntry.finalHeap beforeEntry p args := by
    simpa only [Transition.Events.Observation.terminates.injEq, CBody.Result.mk.injEq] using enterResult
  obtain ⟨enterEvents, enterStatus, sameEntered⟩ := enterEqual
  subst actualEntered
  obtain ⟨duringObserved, sameExit⟩ := certified.duringCalls.determines duringCalls
  subst actualExit
  have exitResult := (certified.exitCall _).mp exitCall
  have exitEqual : observation.exitEvents = [] ∧ observation.exitStatus = .integer 0 ∧
      after = InitializationBodies.exitHeap atExit p kind := by
    simpa only [Transition.Events.Observation.terminates.injEq, CBody.Result.mk.injEq] using exitResult
  obtain ⟨exitEvents, exitStatus, final⟩ := exitEqual
  refine ⟨?_, final⟩
  cases observation
  simp_all only [expectedObservation]

theorem Certificate.execution_iff [CInterface] {program : CCalls.Events.Program E}
    (certified : Certificate model program p buffers args kind state time heap before during beforeEntry atExit) :
    Executed program p buffers args heap before during observation after ↔
      observation = expectedObservation model state time args before during ∧
      after = InitializationBodies.exitHeap atExit p kind := by
  constructor
  · exact certified.determines
  · rintro ⟨rfl, rfl⟩
    exact certified.executes

end Rumoca.FMI3.InitializationAccess
end
