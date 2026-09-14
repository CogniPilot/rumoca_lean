import RumocaFMI3.StaticErrorCalls
import RumocaFMI3.LoggingContract

/-! Complete termination calls in the static object interface. Independent
lifecycle predicates determine acceptance; rejection retains optional logging
and all represented callback outcomes. Native callbacks and ABI are separate. -/
noncomputable section
namespace Rumoca.FMI3.Termination
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory
open CLiteral.Interface

def signature : Signature := ⟨"fmi3Status", "fmi3Terminate", [⟨"fmi3Instance", "instance", false⟩]⟩

theorem body (model : Solve.FMI3Model source) :
    Runtime.body model signature = Runtime.require .terminate ++ [Runtime.setMode .terminated, Runtime.ok] := by
  simp [Runtime.body, signature]

theorem closed (model : Solve.FMI3Model source) :
    (Runtime.body model signature).all CBodyEmbedding.closedBlocks = true :=
  BodyEmbedding.body_closed model signature

theorem body_agrees (model : Solve.FMI3Model source) (objects : Objects) (literals : CLiteralAddresses) :
    CodeAgrees (cInterface literals) (executionInterface objects literals) (Runtime.body model signature) := by
  rw [body]
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, Runtime.require, Runtime.instancePrefix,
    Runtime.modeGuard, Runtime.allowedExpression, permittedModes, Runtime.put,
    Runtime.setMode, Runtime.mode, Runtime.ok, Runtime.reject, Runtime.fail,
    Runtime.branch, Runtime.ret, Runtime.any, Runtime.both, Runtime.either,
    Runtime.negate, Runtime.eqv, Runtime.field, Runtime.call, Runtime.v, Runtime.n,
    Expr.nullPointer, executionInterface, objectConstants]

theorem call_behaviors {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p : Address) (kind : Kind) (mode : Mode),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      load heap (p.member "kind") = some (.integer kind.code) →
      heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
      Reference.Allowed .terminate kind mode →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling signature.name [.pointer (some p)] heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, LifecycleBodies.writeMode heap p .terminated⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program heap p kind mode defined hk hm allowed behavior
  have executed := LifecycleBodies.terminate_run (static := ⟨literals⟩) model signature rfl heap p kind mode hk hm allowed
  have agreement := body_run_agreement (cInterface literals) (executionInterface objects literals)
    (StaticInitialization.interface_types objects literals) rfl 5
    (.running (Runtime.body model signature) (HistoryBodies.parameters p) heap) (body_agrees model objects literals)
  have parameters : @CCalls.parameters (executionInterface objects literals) signature.parameters
      [.pointer (some p)] = some (HistoryBodies.parameters p) := rfl
  exact CCalls.Events.body_call_behaviors program (Runtime.function model signature) _ _ heap _ (.integer 0) 5
    defined parameters (closed model) (agreement.symm.trans executed) rfl behavior

theorem null_behaviors {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling signature.name [.pointer none] heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program heap defined
  apply StaticInitialization.null_call objects literals program (Runtime.function model signature)
    [Runtime.modeGuard .terminate, Runtime.setMode .terminated, Runtime.ok]
    [.pointer none] StateProofs.nullParameters heap defined rfl
    (by simp [Runtime.function, body, Runtime.require, List.append_assoc]) rfl
    (closed model) (body_agrees model objects literals)
  all_goals simp [StateProofs.nullParameters]

theorem failure_prefix (model : Solve.FMI3Model source) (literals : CLiteralAddresses)
    (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (denied : ¬ Reference.Allowed .terminate kind mode) :
    @GuardedCalls.FailurePrefix (cInterface literals) (Runtime.function model signature)
      [.pointer (some p)] heap p ErrorCalls.rejectionMessage heap := by
  letI : CInterface := cInterface literals
  have reached := LifecycleGuard.reject_prefix (static := ⟨literals⟩) (HistoryBodies.parameters p) heap p
    .terminate kind mode [Runtime.setMode .terminated, Runtime.ok]
    (by simp [HistoryBodies.parameters]) (by simp [HistoryBodies.parameters]) hk hm denied
  refine ⟨rfl, closed model, HistoryBodies.parameters p,
    CBody.bind (HistoryBodies.parameters p) "m" (.pointer (some p)),
    [Runtime.setMode .terminated, Runtime.ok], 3, rfl, ?_, ?_, ?_⟩
  · simpa only [Runtime.function, body] using reached
  · simp [HistoryBodies.parameters, CBody.bind]
  · simp [CBody.bind, CBody.resolve]

structure QuietContract [interface : CInterface] (program : CCalls.Events.Program E) : Prop where
  successful : ∀ (heap : Heap) (p : Address) (kind : Kind) (mode : Mode),
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    Reference.Allowed .terminate kind mode →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name [.pointer (some p)] heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, LifecycleBodies.writeMode heap p .terminated⟩
  null : ∀ heap behavior, (CCalls.Events.machine program).Behaves
    (.calling signature.name [.pointer none] heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 3, heap⟩

def SuppressedContract [interface : CInterface] (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ (p : Address) (kind : Kind) (mode : Mode) (logger : Option Address) (logging : Bool),
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (boolean logging) →
    (logger = none ∨ logging = false) → ¬ Reference.Allowed .terminate kind mode →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name [.pointer (some p)] heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

def LoggedContract [interface : CInterface] (program : CCalls.Events.Program Invocation)
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
    ¬ Reference.Allowed .terminate kind mode →
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name [.pointer (some p)] heap .done) behavior ↔
      (∃ value after, effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after ∧
        behavior = .terminates [⟨name, Logging.arguments environment category message⟩] ⟨.integer 3, after⟩) ∨
      ((∀ value after, ¬ effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after) ∧ behavior = .wrong [])) ∧
    (∀ value after, effect.execute (Logging.arguments environment category message)
      (LifecycleBodies.writeMode heap p .terminated) value after →
      Stored signed after category "logStatus" ∧ Stored signed after message ErrorCalls.rejectionMessage)

theorem quiet_correct {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      QuietContract program := by
  letI : CInterface := executionInterface objects literals
  intro program defined
  exact ⟨fun heap p kind mode => call_behaviors objects literals model program heap p kind mode defined,
    fun heap => null_behaviors objects literals model program heap defined⟩

theorem suppressed_correct {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (message : Address) (heap : Heap),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals ErrorCalls.rejectionMessage = some message → SuppressedContract program heap := by
  letI : CInterface := executionInterface objects literals
  intro program message heap defined helper messageBound p kind mode logger logging hk hm hl hg suppressed denied behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  exact StaticErrors.failure_suppressed_behaviors (ErrorContext.static objects literals) program (Runtime.function model signature)
    [.pointer (some p)] heap heap p message ErrorCalls.rejectionMessage _ logger logging
    (body_agrees model objects literals) (failure_prefix model literals heap p kind mode hk modeLoaded denied)
    defined helper messageBound hm hl hg suppressed behavior

theorem logged_correct (objects : Objects) (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program Invocation) (category message : Address) (heap : Heap) (signed : Bool),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "logStatus" = some category → literals ErrorCalls.rejectionMessage = some message →
      Stored signed heap category "logStatus" → Stored signed heap message ErrorCalls.rejectionMessage →
      LoggedContract program category message heap signed := by
  letI : CInterface := executionInterface objects literals
  intro program category message heap signed defined helper categoryBound messageBound categoryStored messageStored
    p logger environment kind mode name effect address external hk hm hl hg he denied
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have all := StaticErrors.failure_all_behaviors (ErrorContext.static objects literals) program (Runtime.function model signature)
    [.pointer (some p)] heap heap p message category logger ErrorCalls.rejectionMessage name environment _
    (External.observed (Logging.signature name) effect) (body_agrees model objects literals)
    (failure_prefix model literals heap p kind mode hk modeLoaded denied) defined helper
    messageBound address external rfl categoryBound hm hl hg he
  constructor
  · intro behavior
    exact (all behavior).trans (observed_choices effect _ _ (fun _ after => ⟨.integer 3, after⟩) behavior)
  · intro value after executed
    have successful := (all (.terminates [⟨name, Logging.arguments environment category message⟩]
      ⟨.integer 3, after⟩)).mpr (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := CCalls.Events.termination_preserves successful
    exact ⟨categoryStored.preserved preserved, messageStored.preserved preserved⟩

end Rumoca.FMI3.Termination
