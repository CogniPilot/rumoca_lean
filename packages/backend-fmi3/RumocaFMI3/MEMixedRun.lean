import RumocaFMI3.MECountExecution

noncomputable section
namespace Rumoca.FMI3.MEMixedRun
open CTree CMemory CBody StaticFactory CCalls.Events

inductive Action where
  | run (action : MENumericalRun.Action)
  | reject (request : MEFailure.Request) (input : Option (BitVec 64))
  | counts (request : CountAccess.Request)

def Action.next (action : Action) (reference : MENumericalHistory.ReferenceState) : MENumericalHistory.ReferenceState :=
  match action with
  | .run (.numerical command) => command.next reference
  | .run (.restart args) => .restart args
  | .reject _ _ => reference.failed
  | .counts request => MECountCalls.next request reference

def Action.clock (action : Action) (clock : Time.Clock) : Time.Clock :=
  match action with
  | .run (.numerical command) => command.clock clock
  | .run (.restart args) => .initial args.start
  | .reject _ _ => clock
  | .counts _ => clock

def Action.Allowed (action : Action) (buffer : Address) (clock : Time.Clock)
    (reference : MENumericalHistory.ReferenceState) : Prop :=
  match action with
  | .run (.numerical command) => command.Allowed reference
  | .run (.restart args) => args.Admissible
  | .reject request input => request.Selected input buffer clock reference
  | .counts request => request.Allowed .me reference.control.mode

def Action.Rejection : Action → Prop
  | .run _ => False
  | .reject _ _ => True
  | .counts request => request.failed = true

/-- Additional caller cells needed by a particular action. Existing numerical
actions keep their previous buffer contract. -/
def Action.CallerRegion : Action → Address → Prop
  | .counts (.get _ output) => fun q => q = output
  | _ => fun _ => False

def Action.Prepared (action : Action) (objects : Objects) (heap : Heap)
    (addresses : String → Address) (buffer : Address) : Prop :=
  match action with
  | .counts request => request.OutputStorage heap ∧ MECountCalls.Separate request objects addresses buffer
  | _ => True

theorem Action.Prepared.preserved (action : Action)
    (prepared : action.Prepared objects before addresses buffer)
    (preserved : CStorage.PreservesOn action.CallerRegion before after) :
    action.Prepared objects after addresses buffer := by
  cases action with
  | run _ | reject _ _ => trivial
  | counts request =>
    cases request with
    | get events output =>
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

structure Returned [CInterface] (model : Solve.FMI3Model source) (objects : Objects)
    (owners : SlotOwners.State objects.capacity) (config : Configuration)
    (p : Address) (addresses : String → Address) (buffer : Address) (heap after : Heap)
    (reference : MENumericalHistory.ReferenceState) (clock : Time.Clock) (action : Action)
    (observed : List (MENumericalHistory.Observation Invocation)) : Prop where
  stored : MENumericalHistory.Stored after p (action.clock clock) (action.next reference) addresses buffer
  resetStorage : Reset.Storage after p
  configuration : config.Stored after p
  ownership : SlotOwners.Represents objects.flagsBlock after owners
  observation : action.Observed model reference observed
  readonly : CReadOnly.Preserves heap after
  frame : ∀ q, MEFailure.Protected objects addresses buffer q → MENumericalRun.Outside p addresses buffer q → after q = heap q
  storage : ∀ region, config.StoragePolicy region → CStorage.PreservesOn region heap after

/-- The finite history certificate branches over all returning outcomes. A
non-returning callback retains its contract and has no invented continuation. -/
inductive Trace [CInterface] (model : Solve.FMI3Model source) (objects : Objects)
    (owners : SlotOwners.State objects.capacity) (config : Configuration)
    (program : Program Invocation) (p : Address) (addresses : String → Address) (buffer : Address) :
    Heap → MENumericalHistory.ReferenceState → Time.Clock → List Action →
    MENumericalHistory.ReferenceState → Time.Clock → Prop where
  | nil : MENumericalHistory.Stored heap p clock reference addresses buffer → Reset.Storage heap p →
      config.Stored heap p → SlotOwners.Represents objects.flagsBlock heap owners →
      Trace model objects owners config program p addresses buffer heap reference clock [] reference clock
  | cons : ActionContract program p addresses buffer heap action returns blocked →
      (∀ observed after epochs, returns observed after epochs →
        Returned model objects owners config p addresses buffer heap after reference clock action observed) →
      (∀ observed after epochs, returns observed after epochs →
        Trace model objects owners config program p addresses buffer after (action.next reference)
          (action.clock clock) rest final finalClock) →
      Trace model objects owners config program p addresses buffer heap reference clock (action :: rest) final finalClock

theorem Trace.completed [CInterface] {program : Program Invocation} {model : Solve.FMI3Model source}
    {owners : SlotOwners.State objects.capacity} {config : Configuration}
    (certified : Trace model objects owners config program p addresses buffer heap reference clock actions final finalClock)
    (completed : Completed program p addresses buffer heap actions observed after epochs) :
    MENumericalHistory.Stored after p finalClock final addresses buffer ∧ Reset.Storage after p ∧
    config.Stored after p ∧ SlotOwners.Represents objects.flagsBlock after owners ∧
    CReadOnly.Preserves heap after ∧
    (∀ q, MEFailure.Protected objects addresses buffer q → MENumericalRun.Outside p addresses buffer q → after q = heap q) := by
  induction completed generalizing reference clock final finalClock with
  | nil => cases certified with
    | nil stored reset config ownership => exact ⟨stored, reset, config, ownership, .refl _, fun _ _ _ => rfl⟩
  | cons performed _ ih =>
    cases certified with
    | cons called returned following =>
      have outcome := called.returned performed
      have next := returned _ _ _ outcome
      obtain ⟨stored, reset, config, ownership, readonly, frame⟩ := ih (following _ _ _ outcome)
      exact ⟨stored, reset, config, ownership, next.readonly.trans readonly,
        fun q guarded outside => (frame q guarded outside).trans (next.frame q guarded outside)⟩

/-- Original caller object descriptions survive every completed history
under the independently supplied universal logger storage policy. -/
theorem Trace.storage [CInterface] {program : Program Invocation} {model : Solve.FMI3Model source}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {config : Configuration}
    (certified : Trace model objects owners config program p addresses buffer heap reference clock actions final finalClock)
    (completed : Completed program p addresses buffer heap actions observed after epochs)
    (policy : config.StoragePolicy region) : CStorage.PreservesOn region heap after := by
  induction completed generalizing reference clock final finalClock with
  | nil => exact .refl _ _
  | cons performed _ ih =>
    cases certified with
    | cons called returned following =>
      have outcome := called.returned performed
      exact ((returned _ _ _ outcome).storage region policy).trans (ih (following _ _ _ outcome))

end Rumoca.FMI3.MEMixedRun
end
