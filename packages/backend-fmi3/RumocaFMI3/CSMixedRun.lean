import RumocaFMI3.CSLoggingCalls
import RumocaFMI3.CSRunProgress
import RumocaFMI3.CSRunLoggedExecution

noncomputable section
namespace Rumoca.FMI3.CSMixedRun
open CTree CMemory CBody StaticFactory CCalls.Events

/-- Lifecycle and logging surround the existing numerical CS actions. -/
inductive Action where
  | run (action : CSRun.Action)
  | logging (request : DebugLogging.Request)

def Action.loggingUpdate : Action → Option Bool
  | .run _ => none
  | .logging request => request.loggingUpdate

def loggingUpdate : List Action → Option Bool
  | [] => none
  | action :: rest => (loggingUpdate rest).orElse fun _ => action.loggingUpdate

theorem loggingUpdate_cons_getD (action : Action) (rest : List Action) (enabled : Bool) :
    (loggingUpdate (action :: rest)).getD enabled =
      (loggingUpdate rest).getD (action.loggingUpdate.getD enabled) := by
  cases found : loggingUpdate rest <;> simp [loggingUpdate, found]

def Action.ReaderRegion : Action → Address → Prop
  | .run _ => fun _ => False
  | .logging request => request.Region

def Action.Prepared : Action → Heap → Prop
  | .run _ => fun _ => True
  | .logging request => request.Inputs

theorem Action.Prepared.framed (action : Action) (prepared : action.Prepared before)
    (frame : ∀ q, action.ReaderRegion q → after q = before q) : action.Prepared after := by
  cases action with
  | run _ => trivial
  | logging request => exact DebugLogging.Request.Inputs.framed prepared frame

inductive Change (header : CFenv.Header) (p : Address) (buffers : StepEntry.Buffers) :
    CSRun.Reference → Action → CSRun.Reference → Int → Prop where
  | run : CSRun.Change header p buffers before action after status →
      Change header p buffers before (.run action) after status
  | logging : Change header p buffers before (.logging request)
      (CSLoggingCalls.next request before) (if request.failed then 3 else 0)

inductive ReferenceTrace (header : CFenv.Header) (p : Address) (buffers : StepEntry.Buffers) :
    CSRun.Reference → List Action → CSRun.Reference → List Int → Prop where
  | nil : ReferenceTrace header p buffers reference [] reference []
  | cons {before next final : CSRun.Reference} : Change header p buffers before action next status →
      ReferenceTrace header p buffers next rest final statuses →
      ReferenceTrace header p buffers before (action :: rest) final (status :: statuses)

/-- The raw relation contains no reference state, expected status or future
heap premise. A numerical restart retains its three actual public calls. -/
inductive Performed [CInterface] (program : Program Invocation) (p : Address) :
    Heap → Action → Value → List Invocation → Heap → Prop where
  | run : CSRun.Performed program p heap action status events after →
      Performed program p heap (.run action) (.integer status) events after
  | logging : (machine program).Behaves
      (.calling (request.call p).1 (request.call p).2 heap .done)
      (.terminates events ⟨status, after⟩) →
      Performed program p heap (.logging request) status events after

inductive Completed [CInterface] (program : Program Invocation) (p : Address) :
    Heap → List Action → List Value → List Invocation → Heap → Prop where
  | nil : Completed program p heap [] [] [] heap
  | cons : Performed program p heap action status events middle →
      Completed program p middle rest statuses later after →
      Completed program p heap (action :: rest) (status :: statuses) (events ++ later) after

inductive Faulted [CInterface] (program : Program Invocation) (p : Address) : Heap → Action → Prop where
  | run : CSRun.Faulted program p heap action → Faulted program p heap (.run action)
  | logging : (machine program).Behaves
      (.calling (request.call p).1 (request.call p).2 heap .done) (.wrong []) →
      Faulted program p heap (.logging request)

inductive Stopped [CInterface] (program : Program Invocation) (p : Address) : Heap → List Action → Prop where
  | here : Faulted program p heap action → Stopped program p heap (action :: rest)
  | later : Performed program p heap action status events middle →
      Stopped program p middle rest → Stopped program p heap (action :: rest)

/-- A branching contract reuses numerical call semantics and the actual
prepared logging setter, including every callback return and no-return case. -/
inductive ActionContract [CInterface] (program : Program Invocation) (p : Address) :
    Heap → Action → (List Invocation → Value → Heap → Prop) → Prop → Prop where
  | run : CSRun.ActionContract program p heap action status outcomes blocked →
      ActionContract program p heap (.run action)
        (fun events value after => value = .integer status ∧ outcomes events after) blocked
  | logging : CSLoggingCalls.Contract model program objects owners capability enabled
      heap p buffers reference request outcomes blocked →
      ActionContract program p heap (.logging request) outcomes blocked

theorem ActionContract.returned [CInterface] {program : Program Invocation}
    (certified : ActionContract program p heap action returns blocked)
    (performed : Performed program p heap action status events after) : returns events status after := by
  cases performed with
  | run executed => cases certified with
    | run called =>
      obtain ⟨same, outcome⟩ := called.performed_status executed
      exact ⟨congrArg Value.integer same, outcome⟩
  | logging executed => cases certified with
    | logging called =>
      rcases (called.behaviors _).mp executed with ⟨_, _, _, outcome, same⟩ | ⟨_, impossible⟩
      · cases same
        exact outcome
      · cases impossible

theorem ActionContract.realizes [CInterface] {program : Program Invocation}
    (certified : ActionContract program p heap action returns blocked)
    (outcome : returns events status after) : Performed program p heap action status events after := by
  cases certified with
  | run called =>
    obtain ⟨rfl, returned⟩ := outcome
    exact .run (called.realizes returned)
  | logging called =>
    exact .logging ((called.behaviors _).mpr (Or.inl ⟨events, status, after, outcome, rfl⟩))

theorem ActionContract.performed_iff [CInterface] {program : Program Invocation}
    (certified : ActionContract program p heap action returns blocked) :
    Performed program p heap action status events after ↔ returns events status after :=
  ⟨certified.returned, certified.realizes⟩

theorem ActionContract.faulted_iff [CInterface] {program : Program Invocation}
    (certified : ActionContract program p heap action returns blocked) :
    Faulted program p heap action ↔ blocked := by
  constructor
  · intro actual
    cases actual with
    | run faulted => cases certified with
      | run called => exact called.faulted_iff.mp faulted
    | logging faulted => cases certified with
      | logging called =>
        rcases (called.behaviors _).mp faulted with ⟨_, _, _, _, impossible⟩ | ⟨blocked, _⟩
        · cases impossible
        · exact blocked
  · intro blocked
    cases certified with
    | run called => exact .run (called.faulted_iff.mpr blocked)
    | logging called => exact .logging ((called.behaviors _).mpr (Or.inr ⟨blocked, rfl⟩))

theorem ActionContract.progress [CInterface] {program : Program Invocation}
    (certified : ActionContract program p heap action returns blocked) :
    (∃ events status after, returns events status after ∧ Performed program p heap action status events after) ∨
      (blocked ∧ Faulted program p heap action) := by
  have available : (∃ events status after, returns events status after) ∨ blocked := by
    cases certified with
    | run called =>
      rcases called.progress with ⟨events, after, returned, _⟩ | ⟨blocked, _⟩
      · exact Or.inl ⟨events, _, after, rfl, returned⟩
      · exact Or.inr blocked
    | logging called => exact called.available
  rcases available with ⟨events, status, after, returned⟩ | blocked
  · exact Or.inl ⟨events, status, after, returned, certified.realizes returned⟩
  · exact Or.inr ⟨blocked, certified.faulted_iff.mpr blocked⟩

def Action.Observed (action : Action) (buffers : StepEntry.Buffers)
    (reference : CSRun.Reference) (expected : Int) (events : List Invocation) (status : Value) (heap : Heap) : Prop :=
  status = .integer expected ∧ match action with
  | .run action => CSRun.Observation buffers reference action expected heap
  | .logging request => CSLoggingCalls.CorrectObservation request events status

structure Returned [CInterface] (objects : Objects) (owners : SlotOwners.State objects.capacity)
    (model : Solve.Model source) (capability : Logging.Capability) (enabled : Bool)
    (p : Address) (buffers : StepEntry.Buffers) (before after : Heap)
    (reference : CSRun.Reference) (action : Action) (expected : Int) (events : List Invocation) (status : Value) : Prop where
  stored : CSRun.Stored model after p buffers reference
  configuration : capability.Configured after p (action.loggingUpdate.getD enabled)
  retention : InitializationProtocol.Retention action.loggingUpdate p before after
  ownership : SlotOwners.Represents objects.flagsBlock after owners
  observed : action.Observed buffers reference expected events status after
  readonly : CReadOnly.Preserves before after
  frame : ∀ q, CSRun.Protected objects buffers q → CSRun.Outside p buffers q → after q = before q
  storage : ∀ region, capability.Requires (fun _ effect =>
    ∀ args before value after, effect.execute args before value after → CStorage.PreservesOn region before after) →
    CStorage.PreservesOn region before after
  callerFrame : ∀ region : Address → Prop, capability.Requires (fun _ effect =>
    ∀ args before value after, effect.execute args before value after → ∀ q, region q → after q = before q) →
    ∀ q, region q → CSRun.Outside p buffers q → after q = before q

inductive Trace [CInterface] (header : CFenv.Header) (objects : Objects) (owners : SlotOwners.State objects.capacity)
    (model : Solve.Model source) (capability : Logging.Capability) (program : Program Invocation)
    (p : Address) (buffers : StepEntry.Buffers) :
    Heap → Bool → CSRun.Reference → List Action → CSRun.Reference → List Int → Prop where
  | nil : CSRun.Stored model heap p buffers reference → capability.Configured heap p enabled →
      SlotOwners.Represents objects.flagsBlock heap owners →
      Trace header objects owners model capability program p buffers heap enabled reference [] reference []
  | cons {before next final : CSRun.Reference} : Change header p buffers before action next status →
      ActionContract program p heap action returns blocked →
      (∀ events value after, returns events value after →
        Returned objects owners model capability enabled p buffers heap after next action status events value) →
      (∀ events value after, returns events value after →
        Trace header objects owners model capability program p buffers after (action.loggingUpdate.getD enabled) next rest final statuses) →
      Trace header objects owners model capability program p buffers heap enabled before (action :: rest) final (status :: statuses)

theorem Trace.progress [CInterface] {program : Program Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}
    (certified : Trace header objects owners model capability program p buffers heap enabled before actions final statuses) :
    (∃ observed events after, Completed program p heap actions observed events after) ∨
      Stopped program p heap actions := by
  induction certified with
  | nil => exact Or.inl ⟨[], [], _, .nil⟩
  | cons _ called _ _ ih =>
    rcases called.progress with ⟨events, status, middle, outcome, performed⟩ | ⟨_, faulted⟩
    · rcases ih events status middle outcome with ⟨observed, later, after, completed⟩ | stopped
      · exact Or.inl ⟨_, _, after, .cons performed completed⟩
      · exact Or.inr (.later performed stopped)
    · exact Or.inr (.here faulted)

theorem Trace.completed [CInterface] {program : Program Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}
    (certified : Trace header objects owners model capability program p buffers heap enabled before actions final statuses)
    (completed : Completed program p heap actions observed events after) :
    observed = statuses.map Value.integer ∧ CSRun.Stored model after p buffers final ∧
    capability.Configured after p ((loggingUpdate actions).getD enabled) ∧
    InitializationProtocol.Retention (loggingUpdate actions) p heap after ∧
    SlotOwners.Represents objects.flagsBlock after owners ∧ CReadOnly.Preserves heap after ∧
    (∀ q, CSRun.Protected objects buffers q → CSRun.Outside p buffers q → after q = heap q) := by
  induction completed generalizing enabled before final statuses with
  | nil => cases certified with
    | nil stored configured represented => exact ⟨rfl, stored, configured, .refl _ _, represented, .refl _, fun _ _ _ => rfl⟩
  | cons performed _ ih => cases certified with
    | cons _ called returned following =>
      have outcome := called.returned performed
      have next := returned _ _ _ outcome
      obtain ⟨values, stored, configured, retained, represented, readonly, frame⟩ := ih (following _ _ _ outcome)
      refine ⟨?_, stored, ?_, next.retention.trans retained, represented, next.readonly.trans readonly,
        fun q guarded outside => (frame q guarded outside).trans (next.frame q guarded outside)⟩
      · exact congrArg₂ List.cons next.observed.1 values
      · simpa only [loggingUpdate_cons_getD] using configured

theorem Trace.storage [CInterface] {program : Program Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}
    (certified : Trace header objects owners model capability program p buffers heap enabled before actions final statuses)
    (completed : Completed program p heap actions observed events after)
    (policy : capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after → CStorage.PreservesOn region before after)) :
    CStorage.PreservesOn region heap after := by
  induction completed generalizing enabled before final statuses with
  | nil => exact .refl _ _
  | cons performed _ ih => cases certified with
    | cons _ called returned following =>
      have outcome := called.returned performed
      exact ((returned _ _ _ outcome).storage region policy).trans (ih (following _ _ _ outcome))

theorem Trace.callerFrame [CInterface] {program : Program Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}
    {region : Address → Prop}
    (certified : Trace header objects owners model capability program p buffers heap enabled before actions final statuses)
    (completed : Completed program p heap actions observed events after)
    (policy : capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after → ∀ q, region q → after q = before q)) :
    ∀ q, region q → CSRun.Outside p buffers q → after q = heap q := by
  induction completed generalizing enabled before final statuses with
  | nil => exact fun _ _ _ => rfl
  | cons performed _ ih => cases certified with
    | cons _ called returned following =>
      have outcome := called.returned performed
      intro q inside outside
      exact (ih (following _ _ _ outcome) q inside outside).trans
        ((returned _ _ _ outcome).callerFrame region policy q inside outside)

end Rumoca.FMI3.CSMixedRun
end
