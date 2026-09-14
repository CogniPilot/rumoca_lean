import RumocaFMI3.CSRunFrames

noncomputable section
namespace Rumoca.FMI3.CSRun
open CTree CMemory CBody StaticFactory CCalls

/-- Only the FMU's instance pool, reservation storage and caller outputs are
protected. A logger can mutate its private storage, including private atomics. -/
def Protected (objects : Objects) (buffers : StepEntry.Buffers) (query : Address) : Prop :=
  query.block = objects.instances.block ∨ query.block = objects.flagsBlock ∨
    query = buffers.event ∨ query = buffers.terminate ∨ query = buffers.early ∨ query = buffers.last

def ProtectedFrame (objects : Objects) (buffers : StepEntry.Buffers) (before after : Heap) : Prop :=
  ∀ query, Protected objects buffers query → after query = before query

structure Logger [CInterface] where
  pointer : Address
  environment : Option Address
  name : String
  effect : Events.ReturningEffect (Logging.signature name)

def Logger.Stored [CInterface] (logger : Logger) (heap : Heap) (p : Address) : Prop :=
  load heap (p.member "logger") = some (.pointer (some logger.pointer)) ∧
  load heap (p.member "logging") = some (.integer 1) ∧
  load heap (p.member "environment") = some (.pointer logger.environment)

def Logger.Bound [CInterface] (logger : Logger) (program : Events.Program Events.Invocation) : Prop :=
  program.addresses logger.pointer = some logger.name ∧
  program.externals logger.name = some (Events.External.observed (Logging.signature logger.name) logger.effect)

/-- A universal external frame contract, not a selected successful callback
outcome. It requires neither determinism nor the existence of a return. -/
def Logger.Respects [CInterface] (logger : Logger) (objects : Objects) (buffers : StepEntry.Buffers) : Prop :=
  ∀ args before result after, logger.effect.execute args before result after →
    ProtectedFrame objects buffers before after

theorem Retains.logger [CInterface] {logger : Logger} (kept : Retains p before after) (stored : Logger.Stored logger before p) :
    Logger.Stored logger after p := by
  exact ⟨by simpa only [load, kept "logger" (by simp)] using stored.1,
    by simpa only [load, kept "logging" (by simp)] using stored.2.1,
    by simpa only [load, kept "environment" (by simp)] using stored.2.2⟩

theorem ProtectedFrame.run (kept : ProtectedFrame objects buffers before after)
    (inPool : p.block = objects.instances.block) : Frame p buffers before after := by
  exact ⟨fun query inside => kept query (Or.inl (inside.1.trans inPool)),
    kept _ (Or.inr (Or.inr (Or.inl rfl))),
    kept _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    kept _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
    kept _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))⟩

theorem ProtectedFrame.retains (kept : ProtectedFrame objects buffers before after)
    (inPool : p.block = objects.instances.block) : Retains p before after :=
  fun name _ => kept (p.member name) (Or.inl inPool)

theorem ProtectedFrame.owners {owners : SlotOwners.State objects.capacity} (kept : ProtectedFrame objects buffers before after)
    (represented : SlotOwners.Represents objects.flagsBlock before owners) :
    SlotOwners.Represents objects.flagsBlock after owners :=
  fun slot => (kept (AtomicSlots.address objects.flagsBlock slot) (Or.inr (Or.inl rfl))).trans (represented slot)

/-- An action's complete call contract specifies returning alternatives and
an explicit blocked alternative. Restart retains its three separate calls.
The logged constructor retains the actual symbol, arguments and effect relation. -/
inductive ActionContract [CInterface] (program : Events.Program Events.Invocation) (p : Address) :
    Heap → Action → Int → (List Events.Invocation → Heap → Prop) → Prop → Prop where
  | silent {heap after : Heap} {action : Action} {status : Int} :
      Executed program p heap action after status →
      ActionContract program p heap action status (fun events next => events = [] ∧ next = after) False
  | logged {heap callbackHeap : Heap} {request : CSHistory.Request} {outputs : StepEntry.Outputs}
      {status : Int} (name : String) (effect : Events.ReturningEffect (Logging.signature name)) (args : List Value) :
      (∀ behavior, (Events.machine program).Behaves
        (.calling StepEntry.signature.name (StepEntry.arguments (some p) request.point request.step request.flag outputs) heap .done) behavior ↔
        (∃ value after, effect.execute args callbackHeap value after ∧
          behavior = .terminates [⟨name, args⟩] ⟨.integer status, after⟩) ∨
        ((∀ value after, ¬ effect.execute args callbackHeap value after) ∧ behavior = .wrong [])) →
      ActionContract program p heap (.step request outputs) status
        (fun events after => events = [⟨name, args⟩] ∧ ∃ value, effect.execute args callbackHeap value after)
        (∀ value after, ¬ effect.execute args callbackHeap value after)

theorem ActionContract.step_behaviors [CInterface] {program : Events.Program Events.Invocation}
    (certified : ActionContract program p heap (.step request outputs) status returns blocked) :
    ∀ behavior, (Events.machine program).Behaves
      (.calling StepEntry.signature.name (StepEntry.arguments (some p) request.point request.step request.flag outputs) heap .done) behavior ↔
      (∃ events after, returns events after ∧ behavior = .terminates events ⟨.integer status, after⟩) ∨
        (blocked ∧ behavior = .wrong []) := by
  cases certified with
  | silent executed =>
    cases executed with
    | step called => intro behavior; simpa [and_assoc] using called behavior
  | logged name effect args called =>
    intro behavior
    rw [called behavior]
    apply or_congr _ Iff.rfl
    constructor
    · rintro ⟨value, after, performed, same⟩
      exact ⟨_, after, ⟨rfl, value, performed⟩, same⟩
    · rintro ⟨events, after, ⟨rfl, value, performed⟩, same⟩
      exact ⟨value, after, performed, same⟩

/-- The persistent guarantee for every returned branch. Only protected cells
outside this call's instance/outputs have an unchanged-value guarantee; private
logger memory is deliberately absent from that frame. -/
structure Returned [CInterface] (objects : Objects) (logger : Logger) (owners : SlotOwners.State objects.capacity)
    (model : Solve.Model source) (p : Address) (buffers : StepEntry.Buffers)
    (before after : Heap) (reference : Reference) (action : Action) (status : Int) : Prop where
  stored : Stored model after p buffers reference
  logging : logger.Stored after p
  ownership : SlotOwners.Represents objects.flagsBlock after owners
  observed : Observation buffers reference action status after
  retained : Retains p before after
  readonly : CReadOnly.Preserves before after
  framed : ∀ query, Protected objects buffers query → Outside p buffers query → after query = before query

/-- A finite reference history induces a branching proof for all returning
callback outcomes. If a callback has no modeled return, ActionContract keeps
its wrong behavior and no continuation is invented. -/
inductive LoggedTrace [CInterface] (objects : Objects) (logger : Logger) (owners : SlotOwners.State objects.capacity)
    (model : Solve.Model source) (program : Events.Program Events.Invocation)
    (p : Address) (buffers : StepEntry.Buffers) :
    Heap → Reference → List Action → Reference → List Int → Prop where
  | nil : Stored model heap p buffers reference → logger.Stored heap p →
      SlotOwners.Represents objects.flagsBlock heap owners →
      LoggedTrace objects logger owners model program p buffers heap reference [] reference []
  | cons {heap : Heap} {before next final : Reference} {action : Action} {rest : List Action}
      {status : Int} {statuses : List Int} {returns : List Events.Invocation → Heap → Prop} {blocked : Prop} :
      ActionContract program p heap action status returns blocked →
      (∀ events after, returns events after →
        Returned objects logger owners model p buffers heap after next action status) →
      (∀ events after, returns events after →
        LoggedTrace objects logger owners model program p buffers after next rest final statuses) →
      LoggedTrace objects logger owners model program p buffers heap before (action :: rest) final (status :: statuses)

end Rumoca.FMI3.CSRun

namespace Rumoca.FMI3.CSRun
open CTree CMemory CBody StaticFactory CCalls

/-- Returned public actions, specified solely by the actual C machine.
Reset/reinitialization retains all three calls and their intermediate heaps. -/
inductive Performed [CInterface] (program : Events.Program Events.Invocation) (p : Address) :
    Heap → Action → Int → List Events.Invocation → Heap → Prop where
  | step : (Events.machine program).Behaves
      (.calling StepEntry.signature.name (StepEntry.arguments (some p) request.point request.step request.flag outputs) heap .done)
      (.terminates events ⟨.integer status, after⟩) →
      Performed program p heap (.step request outputs) status events after
  | restart {heap resetHeap enteredHeap after : Heap} {args : Initialization.Arguments} :
      (Events.machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] heap .done)
        (.terminates resetEvents ⟨.integer 0, resetHeap⟩) →
      (Events.machine program).Behaves
        (.calling InitializationCalls.signature.name
          (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) resetHeap .done)
        (.terminates enterEvents ⟨.integer 0, enteredHeap⟩) →
      (Events.machine program).Behaves
        (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) enteredHeap .done)
        (.terminates exitEvents ⟨.integer 0, after⟩) →
      Performed program p heap (.restart args) 0 (resetEvents ++ enterEvents ++ exitEvents) after

/-- Complete action contracts cover every actually returning action, not
just a selected callback branch. -/
theorem ActionContract.returned [CInterface] {program : Events.Program Events.Invocation}
    (certified : ActionContract program p heap action status returns blocked)
    (performed : Performed program p heap action status events after) : returns events after := by
  cases performed with
  | step called =>
    rcases (certified.step_behaviors _).mp called with ⟨trace, next, returned, same⟩ | ⟨_, impossible⟩
    · cases same
      exact returned
    · cases impossible
  | restart resetCall enterCall exitCall =>
    cases certified with
    | silent executed =>
      cases executed with
      | restart reset enter leave =>
        have first := (reset _).mp resetCall
        cases first
        have second := (enter _).mp enterCall
        cases second
        have third := (leave _).mp exitCall
        cases third
        exact ⟨rfl, rfl⟩

/-- A completed host script records actual target calls, statuses and callback
invocations. Its definition contains no source/Solve invariant or certificate. -/
inductive Completed [CInterface] (program : Events.Program Events.Invocation) (p : Address) :
    Heap → List Action → List Int → List Events.Invocation → Heap → Prop where
  | nil : Completed program p heap [] [] [] heap
  | cons : Performed program p heap action status events middle →
      Completed program p middle rest statuses later after →
      Completed program p heap (action :: rest) (status :: statuses) (events ++ later) after

/-- Every completed actual script admitted by the branching certificate
retains the final Solve/source state, original owners and protected frame.
The branching certificate separately retains blocked behavior at each prefix. -/
theorem LoggedTrace.completed [CInterface] {program : Events.Program Events.Invocation}
    {logger : Logger} {owners : SlotOwners.State objects.capacity}
    (certified : LoggedTrace objects logger owners model program p buffers heap before actions final statuses)
    (completed : Completed program p heap actions statuses events after) :
    Stored model after p buffers final ∧ logger.Stored after p ∧
      SlotOwners.Represents objects.flagsBlock after owners ∧ Retains p heap after ∧
      CReadOnly.Preserves heap after ∧
      (∀ query, Protected objects buffers query → Outside p buffers query → after query = heap query) := by
  induction completed generalizing before final with
  | nil =>
    cases certified with
    | nil stored logging ownership => exact ⟨stored, logging, ownership, fun _ _ => rfl, .refl _, fun _ _ _ => rfl⟩
  | cons performed rest ih =>
    cases certified with
    | cons call returned following =>
      have outcome := call.returned performed
      have post := returned _ _ outcome
      obtain ⟨stored, logging, ownership, retained, readonly, framed⟩ := ih (following _ _ outcome)
      exact ⟨stored, logging, ownership, post.retained.trans retained, post.readonly.trans readonly,
        fun query isProtected outside => (framed query isProtected outside).trans (post.framed query isProtected outside)⟩

end Rumoca.FMI3.CSRun
end
