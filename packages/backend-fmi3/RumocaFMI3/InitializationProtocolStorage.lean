import RumocaFMI3.InitializationProtocol

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CMemory StaticFactory

structure Setup (heap : Heap) (p : Address) (args : Initialization.Arguments) : Prop where
  clock : HistoryProofs.Stored heap p (Time.Clock.initial args.start)
  stop : load heap (p.member "stop") = some (.float64 args.stop)
  stopDefined : load heap (p.member "stopDefined") = some (CBody.boolean args.stopDefined)

theorem Setup.entered (heap : Heap) (p : Address) (args : Initialization.Arguments) :
    Setup (InitializationEntry.finalHeap heap p args) p args :=
  ⟨InitializationCalls.stored heap p args, (InitializationEntry.stop heap p args).1,
    (InitializationEntry.stop heap p args).2⟩

theorem Setup.framed (stored : Setup heap p args)
    (frame : ∀ name, name ≠ "mode" → after (p.member name) = heap (p.member name)) :
    Setup after p args := by
  refine ⟨⟨(frame "time" (by decide)).trans stored.clock.time,
    (frame "timeMin" (by decide)).trans stored.clock.minimum,
    (frame "eventTime" (by decide)).trans stored.clock.eventTime,
    (frame "lastCompleted" (by decide)).trans stored.clock.lastCompleted⟩, ?_, ?_⟩
  · simpa only [load, frame "stop" (by decide)] using stored.stop
  · simpa only [load, frame "stopDefined" (by decide)] using stored.stopDefined

def Phase.Configured (phase : Phase) (heap : Heap) (p : Address) (time : Binary64.Value) : Prop :=
  match phase with
  | .initializing args | .initialized args => args.Admissible ∧ time = args.start ∧ Setup heap p args
  | _ => True

theorem Phase.Configured.framed {phase : Phase} (stored : phase.Configured heap p time)
    (frame : ∀ name, name ≠ "mode" → after (p.member name) = heap (p.member name)) :
    phase.Configured after p time := by
  cases phase with
  | instantiated | failed => trivial
  | initializing args | initialized args => exact ⟨stored.1, stored.2.1, stored.2.2.framed frame⟩

structure Stored (heap : Heap) (p : Address) (kind : Kind) (state : State) : Prop where
  instanceStored : Float64Access.Instance heap p kind (state.phase.mode kind) state.value state.time
  reset : Reset.Storage heap p
  configured : state.phase.Configured heap p state.time

theorem Stored.entry (stored : Stored heap p kind state) (phase : state.phase = .instantiated) :
    InitializationCalls.EntryStorage heap p :=
  ⟨⟨stored.reset.time, stored.reset.minimum, stored.reset.event, stored.reset.completed⟩,
    by simpa only [phase, Phase.mode, Mode.code] using stored.instanceStored.mode,
    stored.reset.stop, stored.reset.stopDefined⟩

theorem Stored.access (stored : Stored heap p kind state)
    (request : Float64Access.Request) (afterInstance : Float64Access.Instance after p kind
      (state.phase.mode kind) (request.next state.value) state.time)
    (storage : CStorage.Preserves heap after)
    (fields : ∀ name, after (p.member name) = heap (p.member name)) :
    Stored after p kind ((Action.access request).next state) :=
  ⟨afterInstance, stored.reset.preserved storage, stored.configured.framed (fun name _ => fields name)⟩

theorem Stored.entered (stored : Stored heap p kind state) (args : Initialization.Arguments)
    (phase : state.phase = .instantiated) (admissible : args.Admissible) :
    Stored (InitializationEntry.finalHeap heap p args) p kind ((Action.enter args).next state) := by
  have old : Float64Access.Instance heap p kind .instantiated state.value state.time := by
    simpa only [phase, Phase.mode] using stored.instanceStored
  exact ⟨InitializationAccess.entered_instance old args,
    stored.reset.preserved (InitializationStorage.entered heap p args kind admissible
      (stored.entry phase) old.kind).1, admissible, rfl, Setup.entered heap p args⟩

theorem Stored.exited (stored : Stored heap p kind state) (phase : state.phase = .initializing args) :
    Stored (InitializationBodies.exitHeap heap p kind) p kind (Action.exit.next state) := by
  have old : Float64Access.Instance heap p kind .initialization state.value state.time := by
    simpa only [phase, Phase.mode] using stored.instanceStored
  have configured : args.Admissible ∧ state.time = args.start ∧ Setup heap p args := by
    simpa only [phase, Phase.Configured] using stored.configured
  have frame (name : String) (different : name ≠ "mode") :=
    InitializationBodies.exit_frame heap p (p.member name) kind (by simpa using different)
  simpa only [Action.next, phase, Phase.mode, Phase.Configured] using
    (show Stored (InitializationBodies.exitHeap heap p kind) p kind
      ⟨.initialized args, state.value, state.time⟩ from
      ⟨InitializationAccess.exited_instance old,
        stored.reset.preserved (InitializationStorage.exited heap p kind old.mode).1,
        configured.1, configured.2.1, configured.2.2.framed frame⟩)

theorem Stored.reset_done (model : Solve.FMI3Model source) (stored : Stored heap p kind state) :
    Stored (Reset.finalHeap heap p) p kind State.reset :=
  ⟨stored.instanceStored.reset, stored.reset.preserved
    (Reset.preserves model heap p kind _ stored.reset stored.instanceStored.kind stored.instanceStored.mode_loaded).1, trivial⟩

theorem Stored.rejected (returned : Float64Rejection.Returned objects retained owners request
    heap p kind state.value state.time after) : Stored after p kind ((Action.reject request).next state) :=
  ⟨returned.stored, returned.resetStorage, trivial⟩

/-- Caller storage is retained relative to the original heap. This permits a
later rejected request to reuse buffers of an earlier accepted/rejected call,
without assuming that the later heap already has the required cells. -/
def CallerStorage (objects : Objects) (retained : Address → Prop) (before after : Heap) : Prop :=
  ∀ (base : Address) (type : CType) (count : Nat), ArrayStore.Writable before base type count →
    (∀ i < count, Float64Rejection.Protected objects retained (base.index i)) →
    ArrayStore.Writable after base type count

theorem CallerStorage.refl (objects : Objects) (retained : Address → Prop) (heap : Heap) :
    CallerStorage objects retained heap heap := fun _ _ _ stored _ => stored

theorem CallerStorage.trans (first : CallerStorage objects retained before middle)
    (second : CallerStorage objects retained middle after) : CallerStorage objects retained before after :=
  fun base type count stored guarded => second base type count (first base type count stored guarded) guarded

theorem CallerStorage.ordinary (preserved : CStorage.Preserves before after) :
    CallerStorage objects retained before after := by
  intro base type count stored _ i inside
  obtain ⟨old, cell⟩ := stored i inside
  exact preserved.cell cell

def RequestGuarded (request : Float64Rejection.Request)
    (objects : Objects) (retained : Address → Prop) : Prop :=
  match request with
  | .get .reference (some input) _ n _ _ =>
      ∀ i < n.toNat, Float64Rejection.Protected objects retained (input.index i)
  | .set .entry (some input) (some buffer) n _ _ _ =>
      (∀ i < n.toNat, Float64Rejection.Protected objects retained (input.index i)) ∧
      (∀ i < n.toNat, Float64Rejection.Protected objects retained (buffer.index i))
  | _ => True

theorem CallerStorage.request (kept : CallerStorage objects retained before after)
    (request : Float64Rejection.Request) (stored : request.TransferStorage before)
    (guarded : RequestGuarded request objects retained) : request.TransferStorage after := by
  cases request with
  | get reason input buffer n m refs =>
    cases reason with
    | arrays => trivial
    | reference => cases input with
      | none => exact False.elim stored
      | some input => exact kept _ _ _ stored guarded
  | set reason input buffer n m refs bits =>
    cases reason with
    | lifecycle | arrays => trivial
    | entry => cases input with
      | none => exact False.elim stored
      | some input => cases buffer with
        | none => exact False.elim stored
        | some buffer => exact ⟨kept _ _ _ stored.1 guarded.1, kept _ _ _ stored.2.1 guarded.2, stored.2.2⟩

end Rumoca.FMI3.InitializationProtocol
end
