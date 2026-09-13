import RumocaC.BodyReachability
import RumocaFMI3.TerminationContract
import RumocaFMI3.TimeHistory

noncomputable section
namespace Rumoca.FMI3.EventEntry
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory CLiteral.Interface

inductive Entry where | event | continuous
  deriving DecidableEq

def Entry.command : Entry → Command
  | .event => .enterEvent
  | .continuous => .enterContinuous

def Entry.before : Entry → Mode
  | .event => .continuous
  | .continuous => .event

def Entry.after : Entry → Mode
  | .event => .event
  | .continuous => .continuous

def signature (entry : Entry) : Signature := ⟨"fmi3Status",
  match entry with | .event => "fmi3EnterEventMode" | .continuous => "fmi3EnterContinuousTimeMode",
  [⟨"fmi3Instance", "instance", false⟩]⟩

def tail : Entry → List Stmt
  | .event => Runtime.eventTime ++ [Runtime.setMode .event, Runtime.ok]
  | .continuous => [Runtime.setMode .continuous, Runtime.ok]

def afterHeap (entry : Entry) (heap : Heap) (p : Address) (clock : Time.Clock) : Heap :=
  match entry with
  | .event => HistoryBodies.eventHeap heap p clock
  | .continuous => LifecycleBodies.writeMode heap p .continuous

def afterClock (entry : Entry) (clock : Time.Clock) : Time.Clock :=
  match entry with | .event => clock.event | .continuous => clock

def afterHistory (entry : Entry) (history : Time.History) : Time.History :=
  match entry with | .event => history.event | .continuous => history

theorem body (model : Solve.FMI3Model source) (entry : Entry) :
    Runtime.body model (signature entry) = Runtime.require entry.command ++ tail entry := by
  cases entry <;> simp [Runtime.body, signature, Entry.command, tail, List.append_assoc]

theorem body_agrees (model : Solve.FMI3Model source) (entry : Entry)
    (objects : Objects) (literals : CLiteralAddresses) :
    CodeAgrees (cInterface literals) (executionInterface objects literals)
      (Runtime.body model (signature entry)) := by
  rw [body]
  cases entry <;>
    simp [CodeAgrees, StmtAgrees, ExprAgrees, names, tail, Entry.command,
      Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression,
      permittedModes, Runtime.put, Runtime.setMode, Runtime.mode, Runtime.ok, Runtime.reject,
      Runtime.fail, Runtime.branch, Runtime.ret, Runtime.any, Runtime.both, Runtime.either,
      Runtime.negate, Runtime.eqv, Runtime.field, Runtime.call, Runtime.v, Runtime.n,
      Runtime.eventTime, Runtime.raiseField, Runtime.lt, Expr.nullPointer,
      executionInterface, objectConstants]

theorem allowed (entry : Entry) (kind : Kind) (mode : Mode) :
    Reference.Allowed entry.command kind mode ↔ kind = .me ∧ mode = entry.before := by
  cases entry <;> rfl

theorem query_cases (entry : Entry) (handle : Option Address) (kind : Kind) (mode : Mode) :
    handle = none ∨ ∃ p, handle = some p ∧
      ((kind = .me ∧ mode = entry.before) ∨ ¬ Reference.Allowed entry.command kind mode) := by
  classical
  cases handle with
  | none => exact Or.inl rfl
  | some p =>
    refine Or.inr ⟨p, rfl, ?_⟩
    by_cases accepted : Reference.Allowed entry.command kind mode
    · exact Or.inl ((allowed entry kind mode).mp accepted)
    · exact Or.inr accepted

theorem continuous_run (model : Solve.FMI3Model source) (literals : CLiteralAddresses)
    (heap : Heap) (p : Address)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer 2)⟩) :
    @run (cInterface literals) 5
      (.running (Runtime.body model (signature .continuous)) (HistoryBodies.parameters p) heap) =
      some (.returned ⟨.integer 0, LifecycleBodies.writeMode heap p .continuous⟩) := by
  letI : CInterface := cInterface literals
  have loaded : load heap (p.member "mode") = some (.integer 2) := by simp [load, hm, convert]
  have entered := LifecycleGuard.accept (static := ⟨literals⟩) (HistoryBodies.parameters p) heap p
    .enterContinuous .me .event (tail .continuous)
    (by simp [HistoryBodies.parameters]) (by simp [HistoryBodies.parameters]) hk loaded ⟨rfl, rfl⟩
  rw [body, Entry.command, show 5 = 3 + 2 from rfl, run_add, entered]
  simp [tail, run, next, Runtime.setMode, Runtime.put, Runtime.field, Runtime.v,
    Runtime.mode, Runtime.n, Runtime.ok, Runtime.ret, Mode.code, eval, lvalue,
    HistoryBodies.parameters, CBody.bind, CBody.resolve, constants, Value.address,
    store, hm, convert, LifecycleBodies.writeMode]

theorem call_behaviors {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (entry : Entry) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p : Address) (clock : Time.Clock),
      program.internal.definitions (signature entry).name = some (.tree (Runtime.function model (signature entry))) →
      load heap (p.member "kind") = some (.integer 0) →
      heap (p.member "mode") = some ⟨.int32, true, some (.integer entry.before.code)⟩ →
      (entry = .event → HistoryProofs.Stored heap p clock) →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (signature entry).name [.pointer (some p)] heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, afterHeap entry heap p clock⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program heap p clock defined hk hm stored behavior
  have finiteRun : ∃ n, @run (cInterface literals) n
      (.running (Runtime.body model (signature entry)) (HistoryBodies.parameters p) heap) =
      some (.returned ⟨.integer 0, afterHeap entry heap p clock⟩) := by
    cases entry with
    | event =>
      exact CBody.run_of_reaches (interface := cInterface literals) (HistoryBodies.event_reaches (static := ⟨literals⟩)
        model (signature .event) rfl heap p clock (stored rfl) hk hm)
    | continuous => exact ⟨5, continuous_run model literals heap p hk hm⟩
  obtain ⟨n, executed⟩ := finiteRun
  have agreement := body_run_agreement (cInterface literals) (executionInterface objects literals)
    (StaticInitialization.interface_types objects literals) rfl n
    (.running (Runtime.body model (signature entry)) (HistoryBodies.parameters p) heap)
    (body_agrees model entry objects literals)
  have bound : @CCalls.parameters (executionInterface objects literals) (signature entry).parameters
      [.pointer (some p)] = some (HistoryBodies.parameters p) := by cases entry <;> rfl
  exact CCalls.Events.body_call_behaviors program (Runtime.function model (signature entry)) _ _ heap _ (.integer 0) n
    defined bound (BodyEmbedding.body_closed model (signature entry)) (agreement.symm.trans executed) rfl behavior

theorem null_behaviors {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (entry : Entry) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap),
      program.internal.definitions (signature entry).name = some (.tree (Runtime.function model (signature entry))) →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (signature entry).name [.pointer none] heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program heap defined
  apply StaticInitialization.null_call objects literals program (Runtime.function model (signature entry))
    (Runtime.modeGuard entry.command :: tail entry)
    [.pointer none] StateProofs.nullParameters heap defined rfl
    (by simp [Runtime.function, body, Runtime.require, List.append_assoc]) rfl
    (BodyEmbedding.body_closed model (signature entry)) (body_agrees model entry objects literals)
  all_goals simp [StateProofs.nullParameters]

theorem failure_prefix (model : Solve.FMI3Model source) (entry : Entry) (literals : CLiteralAddresses)
    (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (denied : ¬ Reference.Allowed entry.command kind mode) :
    @GuardedCalls.FailurePrefix (cInterface literals) (Runtime.function model (signature entry))
      [.pointer (some p)] heap p ErrorCalls.rejectionMessage heap := by
  letI : CInterface := cInterface literals
  have reached := LifecycleGuard.reject_prefix (static := ⟨literals⟩) (HistoryBodies.parameters p) heap p
    entry.command kind mode (tail entry)
    (by simp [HistoryBodies.parameters]) (by simp [HistoryBodies.parameters]) hk hm denied
  refine ⟨rfl, BodyEmbedding.body_closed model (signature entry), HistoryBodies.parameters p,
    CBody.bind (HistoryBodies.parameters p) "m" (.pointer (some p)),
    tail entry, 3, rfl, ?_, ?_, ?_⟩
  · simpa only [Runtime.function, body] using reached
  · simp [HistoryBodies.parameters, CBody.bind]
  · simp [CBody.bind, CBody.resolve]

structure QuietContract (entry : Entry) [interface : CInterface] (program : CCalls.Events.Program E) : Prop where
  successful : ∀ (heap : Heap) (p : Address) (clock : Time.Clock),
    load heap (p.member "kind") = some (.integer 0) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer entry.before.code)⟩ →
    (entry = .event → HistoryProofs.Stored heap p clock) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature entry).name [.pointer (some p)] heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, afterHeap entry heap p clock⟩
  null : ∀ heap behavior, (CCalls.Events.machine program).Behaves
    (.calling (signature entry).name [.pointer none] heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 3, heap⟩

def SuppressedContract (entry : Entry) [interface : CInterface] (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ (p : Address) (kind : Kind) (mode : Mode) (logger : Option Address) (logging : Bool),
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (boolean logging) →
    (logger = none ∨ logging = false) → ¬ Reference.Allowed entry.command kind mode →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature entry).name [.pointer (some p)] heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

def LoggedContract (entry : Entry) [interface : CInterface] (program : CCalls.Events.Program Invocation)
    (category message : Address) (heap : Heap) (signed : Bool) : Prop :=
  ∀ (p logger : Address) (environment : Option Address) (kind : Kind) (mode : Mode)
    (name : String) (effect : ReturningEffect (Logging.signature name)),
    program.addresses logger = some name →
    program.externals name = some (External.observed (Logging.signature name) effect) →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    ¬ Reference.Allowed entry.command kind mode →
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature entry).name [.pointer (some p)] heap .done) behavior ↔
      (∃ value after, effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after ∧
        behavior = .terminates [⟨name, Logging.arguments environment category message⟩] ⟨.integer 3, after⟩) ∨
      ((∀ value after, ¬ effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after) ∧ behavior = .wrong [])) ∧
    (∀ value after, effect.execute (Logging.arguments environment category message)
      (LifecycleBodies.writeMode heap p .terminated) value after →
      Stored signed after category "logStatus" ∧ Stored signed after message ErrorCalls.rejectionMessage)

theorem quiet_correct {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (entry : Entry) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E),
      program.internal.definitions (signature entry).name = some (.tree (Runtime.function model (signature entry))) →
      QuietContract entry program := by
  letI : CInterface := executionInterface objects literals
  intro program defined
  exact ⟨fun heap p clock => call_behaviors objects literals model entry program heap p clock defined,
    fun heap => null_behaviors objects literals model entry program heap defined⟩

theorem suppressed_correct {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (entry : Entry) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (message : Address) (heap : Heap),
      program.internal.definitions (signature entry).name = some (.tree (Runtime.function model (signature entry))) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals ErrorCalls.rejectionMessage = some message → SuppressedContract entry program heap := by
  letI : CInterface := executionInterface objects literals
  intro program message heap defined helper messageBound p kind mode logger logging hk hm hl hg suppressed denied behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  exact StaticErrors.failure_suppressed_behaviors objects literals program (Runtime.function model (signature entry))
    [.pointer (some p)] heap heap p message ErrorCalls.rejectionMessage _ logger logging
    (body_agrees model entry objects literals) (failure_prefix model entry literals heap p kind mode hk modeLoaded denied)
    defined helper messageBound hm hl hg suppressed behavior

theorem logged_correct (objects : Objects) (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (entry : Entry) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program Invocation) (category message : Address) (heap : Heap) (signed : Bool),
      program.internal.definitions (signature entry).name = some (.tree (Runtime.function model (signature entry))) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "logStatus" = some category → literals ErrorCalls.rejectionMessage = some message →
      Stored signed heap category "logStatus" → Stored signed heap message ErrorCalls.rejectionMessage →
      LoggedContract entry program category message heap signed := by
  letI : CInterface := executionInterface objects literals
  intro program category message heap signed defined helper categoryBound messageBound categoryStored messageStored
    p logger environment kind mode name effect address external hk hm hl hg he denied
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have all := StaticErrors.failure_all_behaviors objects literals program (Runtime.function model (signature entry))
    [.pointer (some p)] heap heap p message category logger ErrorCalls.rejectionMessage name environment _
    (External.observed (Logging.signature name) effect) (body_agrees model entry objects literals)
    (failure_prefix model entry literals heap p kind mode hk modeLoaded denied) defined helper
    messageBound address external rfl categoryBound hm hl hg he
  constructor
  · intro behavior
    exact (all behavior).trans (observed_choices effect _ _ (fun _ after => ⟨.integer 3, after⟩) behavior)
  · intro value after executed
    have successful := (all (.terminates [⟨name, Logging.arguments environment category message⟩]
      ⟨.integer 3, after⟩)).mpr (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := CCalls.Events.termination_preserves successful
    exact ⟨categoryStored.preserved preserved, messageStored.preserved preserved⟩

end Rumoca.FMI3.EventEntry
