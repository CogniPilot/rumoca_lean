import RumocaFMI3.MENominalExecution
import RumocaFMI3.MELoggingCalls

noncomputable section
namespace Rumoca.FMI3.MEMixedRun
open CTree CMemory CBody StaticFactory CCalls.Events

inductive Action where
  | run (action : MENumericalRun.Action)
  | reject (request : MEFailure.Request) (input : Option (BitVec 64))
  | counts (request : CountAccess.Request)
  | nominals (request : NominalAccess.Request)
  | logging (request : DebugLogging.Request)

def Action.next (action : Action) (reference : MENumericalHistory.ReferenceState) : MENumericalHistory.ReferenceState :=
  match action with
  | .run (.numerical command) => command.next reference
  | .run (.restart args) => .restart args
  | .reject _ _ => reference.failed
  | .counts request => MECountCalls.next request reference
  | .nominals request => MENominalCalls.next request reference
  | .logging request => MELoggingCalls.next request reference

def Action.clock (action : Action) (clock : Time.Clock) : Time.Clock :=
  match action with
  | .run (.numerical command) => command.clock clock
  | .run (.restart args) => .initial args.start
  | .reject _ _ => clock
  | .counts _ => clock
  | .nominals _ => clock
  | .logging _ => clock

def Action.Allowed (action : Action) (buffer : Address) (clock : Time.Clock)
    (reference : MENumericalHistory.ReferenceState) : Prop :=
  match action with
  | .run (.numerical command) => command.Allowed reference
  | .run (.restart args) => args.Admissible
  | .reject request input => request.Selected input buffer clock reference
  | .counts request => request.Allowed .me reference.control.mode
  | .nominals request => request.Allowed .me reference.control.mode
  | .logging _ => True

def Action.Rejection : Action → Prop
  | .run _ => False
  | .reject _ _ => True
  | .counts request => request.failed = true
  | .nominals request => request.failed = true
  | .logging request => request.failed = true

/-- Additional caller cells needed by a particular action. Existing numerical
actions keep their previous buffer contract. -/
def Action.CallerRegion : Action → Address → Prop
  | .counts (.get _ output) => fun q => q = output
  | .nominals (.get output) => fun q => q = output
  | _ => fun _ => False

/-- Borrowed string contents need an exact frame, independently of the
typed output cells described by CallerRegion. -/
def Action.ReaderRegion : Action → Address → Prop
  | .logging request => request.Region
  | _ => fun _ => False

def Action.Prepared (action : Action) (objects : Objects) (heap : Heap)
    (addresses : String → Address) (buffer : Address) : Prop :=
  match action with
  | .counts request => request.OutputStorage heap ∧ MECountCalls.Separate request objects addresses buffer
  | .nominals request => request.OutputStorage heap ∧ MENominalCalls.Separate request objects
  | .logging request => request.Inputs heap
  | _ => True

theorem Action.Prepared.preserved (action : Action)
    (prepared : action.Prepared objects before addresses buffer)
    (preserved : CStorage.PreservesOn action.CallerRegion before after)
    (readers : ∀ q, action.ReaderRegion q → after q = before q) :
    action.Prepared objects after addresses buffer := by
  cases action with
  | run _ | reject _ _ => trivial
  | logging request => exact prepared.framed readers
  | counts request =>
    cases request with
    | get events output =>
      obtain ⟨⟨old, found⟩, separate⟩ := prepared
      exact ⟨preserved.cell rfl found, separate⟩
    | reject _ _ _ => exact prepared
  | nominals request =>
    cases request with
    | get output =>
      obtain ⟨⟨old, found⟩, separate⟩ := prepared
      exact ⟨preserved.cell rfl found, separate⟩
    | reject _ _ _ => exact prepared

/-- Expected statuses/readbacks are postconditions, never restrictions on
the raw target execution relation. Failed-call outputs have no numerical claim. -/
def Action.Observed (action : Action) (model : Solve.FMI3Model source)
    (reference : MENumericalHistory.ReferenceState) (observed : List (MENumericalHistory.Observation Invocation)) : Prop :=
  match action with
  | .run command => observed = (MENumericalRun.observations model reference [command]).map MENumericalHistory.Observation.ok
  | .reject _ _ => ∃ events, observed = [⟨events, .integer 3, none⟩]
  | .counts request => if request.failed then ∃ events, observed = [⟨events, .integer 3, none⟩]
      else observed = [MENumericalHistory.Observation.ok (request.expected model 0)]
  | .nominals request => if request.failed then ∃ events, observed = [⟨events, .integer 3, none⟩]
      else observed = [MENumericalHistory.Observation.ok (request.expected model 0)]
  | .logging request => if request.failed then ∃ events, observed = [⟨events, .integer 3, none⟩]
      else observed = [MENumericalHistory.Observation.ok none]

inductive ReferenceTrace (buffer : Address) : MENumericalHistory.ReferenceState → Time.Clock →
    List Action → MENumericalHistory.ReferenceState → Time.Clock → Prop where
  | nil : ReferenceTrace buffer reference clock [] reference clock
  | cons : action.Allowed buffer clock reference →
      ReferenceTrace buffer (action.next reference) (action.clock clock) rest final finalClock →
      ReferenceTrace buffer reference clock (action :: rest) final finalClock

/-- An actual action records raw statuses, query values and initialization
checkpoints. A rejected setter's caller write is itself a typed target store. -/
inductive Performed [CInterface] (program : Program Invocation) (p : Address)
    (addresses : String → Address) (buffer : Address) : Heap → Action →
    List (MENumericalHistory.Observation Invocation) → Heap → List MENumericalRun.Epoch → Prop where
  | run : MENumericalRun.Executed program p addresses buffer heap [action] observed after epochs →
      Performed program p addresses buffer heap (.run action) observed after epochs
  | reject : MEFailure.Prepares input heap ready buffer →
      (machine program).Behaves (.calling (request.call p).1 (request.call p).2 ready .done)
        (.terminates events ⟨status, after⟩) →
      Performed program p addresses buffer heap (.reject request input) [⟨events, status, none⟩] after []
  | counts : (machine program).Behaves (.calling (request.call p).1 (request.call p).2 heap .done)
        (.terminates events ⟨status, after⟩) →
      Performed program p addresses buffer heap (.counts request)
        [⟨events, status, request.readback after 0⟩] after []
  | nominals : (machine program).Behaves (.calling (request.call p).1 (request.call p).2 heap .done)
        (.terminates events ⟨status, after⟩) →
      Performed program p addresses buffer heap (.nominals request)
        [⟨events, status, request.readback after 0⟩] after []
  | logging : (machine program).Behaves (.calling (request.call p).1 (request.call p).2 heap .done)
        (.terminates events ⟨status, after⟩) →
      Performed program p addresses buffer heap (.logging request) [⟨events, status, none⟩] after []

inductive Completed [CInterface] (program : Program Invocation) (p : Address)
    (addresses : String → Address) (buffer : Address) : Heap → List Action →
    List (MENumericalHistory.Observation Invocation) → Heap → List MENumericalRun.Epoch → Prop where
  | nil : Completed program p addresses buffer heap [] [] heap []
  | cons : Performed program p addresses buffer heap action observed middle epochs →
      Completed program p addresses buffer middle rest values after checkpoints →
      Completed program p addresses buffer heap (action :: rest) (observed ++ values) after (epochs ++ checkpoints)

/-- Complete action contracts keep every returning callback alternative and
the modeled no-return alternative; restart keeps all three separate calls. -/
inductive ActionContract [CInterface] (program : Program Invocation) (p : Address)
    (addresses : String → Address) (buffer : Address) : Heap → Action →
    (List (MENumericalHistory.Observation Invocation) → Heap → List MENumericalRun.Epoch → Prop) → Prop → Prop where
  | run : MENumericalRun.Calls program p addresses buffer heap [action] values after epochs →
      ActionContract program p addresses buffer heap (.run action)
        (fun observed next checkpoints => observed = values.map MENumericalHistory.Observation.ok ∧ next = after ∧ checkpoints = epochs) False
  | quiet : MEFailure.Prepares input heap ready buffer →
      (∀ behavior, (machine program).Behaves (.calling (request.call p).1 (request.call p).2 ready .done) behavior ↔
        behavior = .terminates [] ⟨.integer 3, after⟩) →
      ActionContract program p addresses buffer heap (.reject request input)
        (fun observed next checkpoints => observed = [⟨[], .integer 3, none⟩] ∧ next = after ∧ checkpoints = []) False
  | logged (name : String) (effect : ReturningEffect (Logging.signature name)) (args : List Value) :
      MEFailure.Prepares input heap ready buffer →
      (∀ behavior, (machine program).Behaves (.calling (request.call p).1 (request.call p).2 ready .done) behavior ↔
        (∃ value after, effect.execute args callbackHeap value after ∧
          behavior = .terminates [⟨name, args⟩] ⟨.integer 3, after⟩) ∨
        ((∀ value after, ¬ effect.execute args callbackHeap value after) ∧ behavior = .wrong [])) →
      ActionContract program p addresses buffer heap (.reject request input)
        (fun observed next checkpoints => observed = [⟨[⟨name, args⟩], .integer 3, none⟩] ∧
          checkpoints = [] ∧ ∃ value, effect.execute args callbackHeap value next)
        (∀ value after, ¬ effect.execute args callbackHeap value after)
  | counts (contract : MECountCalls.Contract model program objects owners config heap p addresses buffer
      clock reference request outcomes blocked) :
      ActionContract program p addresses buffer heap (.counts request)
        (fun observed next checkpoints => ∃ events status,
          observed = [⟨events, status, request.readback next 0⟩] ∧ checkpoints = [] ∧ outcomes events status next)
        blocked
  | nominals (contract : MENominalCalls.Contract model program objects owners config heap p addresses buffer
      clock reference request outcomes blocked) :
      ActionContract program p addresses buffer heap (.nominals request)
        (fun observed next checkpoints => ∃ events status,
          observed = [⟨events, status, request.readback next 0⟩] ∧ checkpoints = [] ∧ outcomes events status next)
        blocked
  | logging (contract : MELoggingCalls.Contract program objects owners capability enabled heap p addresses buffer
      clock reference request outcomes blocked) :
      ActionContract program p addresses buffer heap (.logging request)
        (fun observed next checkpoints => ∃ events status,
          observed = [⟨events, status, none⟩] ∧ checkpoints = [] ∧ outcomes events status next)
        blocked

theorem ActionContract.returned [CInterface] {program : Program Invocation}
    (certified : ActionContract program p addresses buffer heap action returns blocked)
    (performed : Performed program p addresses buffer heap action observed after epochs) :
    returns observed after epochs := by
  cases performed with
  | run executed => cases certified with
    | run called => exact called.determines executed
  | reject prepared executed =>
    cases certified with
    | quiet preparation called =>
      have same := MEFailure.Prepares.unique preparation prepared
      cases same
      have result := (called _).mp executed
      cases result
      exact ⟨rfl, rfl, rfl⟩
    | logged name effect args preparation called =>
      have same := MEFailure.Prepares.unique preparation prepared
      cases same
      rcases (called _).mp executed with ⟨value, next, outcome, result⟩ | ⟨_, impossible⟩
      · cases result
        exact ⟨rfl, rfl, value, outcome⟩
      · cases impossible
  | counts executed =>
    cases certified with
    | counts contract =>
      rcases (contract.behaviors _).mp executed with ⟨events, status, next, outcome, same⟩ | ⟨_, impossible⟩
      · cases same
        exact ⟨_, _, rfl, rfl, outcome⟩
      · cases impossible
  | nominals executed =>
    cases certified with
    | nominals contract =>
      rcases (contract.behaviors _).mp executed with ⟨events, status, next, outcome, same⟩ | ⟨_, impossible⟩
      · cases same
        exact ⟨_, _, rfl, rfl, outcome⟩
      · cases impossible
  | logging executed =>
    cases certified with
    | logging contract =>
      rcases (contract.behaviors _).mp executed with ⟨events, status, next, outcome, same⟩ | ⟨_, impossible⟩
      · cases same
        exact ⟨_, _, rfl, rfl, outcome⟩
      · cases impossible

/-- Each certified returning alternative is realized by actual target calls;
this direction prevents the branching certificate from inventing outcomes. -/
theorem ActionContract.realizes [CInterface] {program : Program Invocation}
    (certified : ActionContract program p addresses buffer heap action returns blocked)
    (outcome : returns observed after epochs) :
    Performed program p addresses buffer heap action observed after epochs := by
  cases certified with
  | run called =>
    obtain ⟨rfl, rfl, rfl⟩ := outcome
    exact .run called.executes
  | quiet prepared called =>
    obtain ⟨rfl, rfl, rfl⟩ := outcome
    exact .reject prepared ((called _).mpr rfl)
  | logged name effect args prepared called =>
    obtain ⟨rfl, rfl, value, returned⟩ := outcome
    exact .reject prepared ((called _).mpr (Or.inl ⟨value, after, returned, rfl⟩))
  | counts contract =>
    obtain ⟨events, status, rfl, rfl, returned⟩ := outcome
    exact .counts ((contract.behaviors _).mpr (Or.inl ⟨events, status, after, returned, rfl⟩))
  | nominals contract =>
    obtain ⟨events, status, rfl, rfl, returned⟩ := outcome
    exact .nominals ((contract.behaviors _).mpr (Or.inl ⟨events, status, after, returned, rfl⟩))
  | logging contract =>
    obtain ⟨events, status, rfl, rfl, returned⟩ := outcome
    exact .logging ((contract.behaviors _).mpr (Or.inl ⟨events, status, after, returned, rfl⟩))

def Action.loggingUpdate : Action → Option Bool
  | .logging request => request.loggingUpdate
  | _ => none

def loggingUpdate : List Action → Option Bool
  | [] => none
  | action :: rest => (loggingUpdate rest).orElse fun _ => action.loggingUpdate

/-- Later successful updates supersede earlier flags; failures retain them. -/
theorem loggingUpdate_cons_getD (action : Action) (rest : List Action) (enabled : Bool) :
    (loggingUpdate (action :: rest)).getD enabled =
      (loggingUpdate rest).getD (action.loggingUpdate.getD enabled) := by
  cases following : loggingUpdate rest <;> simp [loggingUpdate, following]

/-- A successful flag change retains the original callable capability.
Numerical state and control-policy updates are separate postconditions. -/
structure Returned [CInterface] (model : Solve.FMI3Model source) (objects : Objects)
    (owners : SlotOwners.State objects.capacity) (capability : Logging.Capability) (enabled : Bool)
    (p : Address) (addresses : String → Address) (buffer : Address) (heap after : Heap)
    (reference : MENumericalHistory.ReferenceState) (clock : Time.Clock) (action : Action)
    (observed : List (MENumericalHistory.Observation Invocation)) : Prop where
  stored : MENumericalHistory.Stored after p (action.clock clock) (action.next reference) addresses buffer
  resetStorage : Reset.Storage after p
  configuration : capability.Configured after p (action.loggingUpdate.getD enabled)
  retention : InitializationProtocol.Retention action.loggingUpdate p heap after
  ownership : SlotOwners.Represents objects.flagsBlock after owners
  observation : action.Observed model reference observed
  readonly : CReadOnly.Preserves heap after
  frame : ∀ q, MEFailure.Protected objects addresses buffer q → MENumericalRun.Outside p addresses buffer q →
    q ≠ p.member "logging" → after q = heap q
  storage : ∀ region, capability.Requires (fun _ effect =>
    ∀ args before value after, effect.execute args before value after → CStorage.PreservesOn region before after) →
    CStorage.PreservesOn region heap after
  callerFrame : ∀ region : Address → Prop, capability.Requires (fun _ effect =>
    ∀ args before value after, effect.execute args before value after → ∀ q, region q → after q = before q) →
    ∀ q, region q → MENumericalRun.Outside p addresses buffer q →
      q ≠ p.member "logging" → ¬ action.CallerRegion q → after q = heap q

inductive Trace [CInterface] (model : Solve.FMI3Model source) (objects : Objects)
    (owners : SlotOwners.State objects.capacity) (capability : Logging.Capability)
    (program : Program Invocation) (p : Address) (addresses : String → Address) (buffer : Address) :
    Heap → Bool → MENumericalHistory.ReferenceState → Time.Clock → List Action →
    MENumericalHistory.ReferenceState → Time.Clock → Prop where
  | nil : MENumericalHistory.Stored heap p clock reference addresses buffer → Reset.Storage heap p →
      capability.Configured heap p enabled → SlotOwners.Represents objects.flagsBlock heap owners →
      Trace model objects owners capability program p addresses buffer heap enabled reference clock [] reference clock
  | cons : ActionContract program p addresses buffer heap action returns blocked →
      (∀ observed after epochs, returns observed after epochs →
        Returned model objects owners capability enabled p addresses buffer heap after reference clock action observed) →
      (∀ observed after epochs, returns observed after epochs →
        Trace model objects owners capability program p addresses buffer after (action.loggingUpdate.getD enabled)
          (action.next reference) (action.clock clock) rest final finalClock) →
      Trace model objects owners capability program p addresses buffer heap enabled reference clock (action :: rest) final finalClock

theorem Trace.completed [CInterface] {program : Program Invocation} {model : Solve.FMI3Model source}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}
    (certified : Trace model objects owners capability program p addresses buffer heap enabled reference clock actions final finalClock)
    (completed : Completed program p addresses buffer heap actions observed after epochs) :
    MENumericalHistory.Stored after p finalClock final addresses buffer ∧ Reset.Storage after p ∧
    capability.Configured after p ((loggingUpdate actions).getD enabled) ∧
    InitializationProtocol.Retention (loggingUpdate actions) p heap after ∧
    SlotOwners.Represents objects.flagsBlock after owners ∧ CReadOnly.Preserves heap after ∧
    (∀ q, MEFailure.Protected objects addresses buffer q → MENumericalRun.Outside p addresses buffer q →
      q ≠ p.member "logging" → after q = heap q) := by
  induction completed generalizing enabled reference clock final finalClock with
  | nil => cases certified with
    | nil stored reset configured ownership =>
      exact ⟨stored, reset, configured, .refl _ _, ownership, .refl _, fun _ _ _ _ => rfl⟩
  | cons performed _ ih =>
    cases certified with
    | cons called returned following =>
      have outcome := called.returned performed
      have next := returned _ _ _ outcome
      obtain ⟨stored, reset, configured, retained, ownership, readonly, frame⟩ := ih (following _ _ _ outcome)
      refine ⟨stored, reset, ?_, next.retention.trans retained, ownership, next.readonly.trans readonly,
        fun q guarded outside different => (frame q guarded outside different).trans (next.frame q guarded outside different)⟩
      simpa only [loggingUpdate_cons_getD] using configured

theorem Trace.storage [CInterface] {program : Program Invocation} {model : Solve.FMI3Model source}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}
    (certified : Trace model objects owners capability program p addresses buffer heap enabled reference clock actions final finalClock)
    (completed : Completed program p addresses buffer heap actions observed after epochs)
    (policy : capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after → CStorage.PreservesOn region before after)) :
    CStorage.PreservesOn region heap after := by
  induction completed generalizing enabled reference clock final finalClock with
  | nil => exact .refl _ _
  | cons performed _ ih =>
    cases certified with
    | cons called returned following =>
      have outcome := called.returned performed
      exact ((returned _ _ _ outcome).storage region policy).trans (ih (following _ _ _ outcome))

theorem Trace.callerFrame [CInterface] {program : Program Invocation} {model : Solve.FMI3Model source}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}
    {region : Address → Prop}
    (certified : Trace model objects owners capability program p addresses buffer heap enabled reference clock actions final finalClock)
    (completed : Completed program p addresses buffer heap actions observed after epochs)
    (policy : capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after → ∀ q, region q → after q = before q)) :
    ∀ q, region q → MENumericalRun.Outside p addresses buffer q → q ≠ p.member "logging" →
      (∀ action ∈ actions, ¬ action.CallerRegion q) → after q = heap q := by
  induction completed generalizing enabled reference clock final finalClock with
  | nil => exact fun _ _ _ _ _ => rfl
  | cons performed _ ih =>
    cases certified with
    | cons called returned following =>
      have outcome := called.returned performed
      intro q inside outside different untouched
      exact (ih (following _ _ _ outcome) q inside outside different
        (fun action member => untouched action (List.mem_cons_of_mem _ member))).trans
        ((returned _ _ _ outcome).callerFrame region policy q inside outside different (untouched _ (by simp)))

end Rumoca.FMI3.MEMixedRun
end
