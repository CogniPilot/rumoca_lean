import RumocaC.BodyReachability
import RumocaFMI3.TerminationContract
import RumocaFMI3.TimeContract

noncomputable section
namespace Rumoca.FMI3.CompletedCalls
open CTree CMemory CBody StaticFactory CLiteral.Interface

def signature : Signature := ⟨"fmi3Status", "fmi3CompletedIntegratorStep",
  [⟨"fmi3Instance", "instance", false⟩,
   ⟨"fmi3Boolean", "noSetFMUStatePriorToCurrentPoint", false⟩,
   ⟨"fmi3Boolean *", "enterEventMode", false⟩,
   ⟨"fmi3Boolean *", "terminateSimulation", false⟩]⟩

def arguments (handle event terminate : Option Address) (flag : Bool) : List Value :=
  [.pointer handle, boolean flag, .pointer event, .pointer terminate]

def parameters (handle event terminate : Option Address) (flag : Bool) : Locals := fun name =>
  if name = "instance" then some (.pointer handle)
  else if name = "enterEventMode" then some (.pointer event)
  else if name = "terminateSimulation" then some (.pointer terminate)
  else if name = "noSetFMUStatePriorToCurrentPoint" then some (boolean flag)
  else none

def tail : List Stmt := [Runtime.out "enterEventMode" (Runtime.n 0),
  Runtime.out "terminateSimulation" (Runtime.n 0)] ++ Runtime.completedTime ++ [Runtime.ok]

theorem body (model : Solve.FMI3Model source) :
    Runtime.body model signature = Runtime.require .completedStep ++
      Runtime.pointerCheck ["enterEventMode", "terminateSimulation"] :: tail := by
  simp [Runtime.body, signature, tail, List.append_assoc]

theorem body_agrees (model : Solve.FMI3Model source) (objects : Objects) (literals : CLiteralAddresses) :
    CodeAgrees (cInterface literals) (executionInterface objects literals) (Runtime.body model signature) := by
  rw [body]
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, tail,
    Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression,
    permittedModes, Runtime.put, Runtime.mode, Runtime.ok, Runtime.reject,
    Runtime.fail, Runtime.branch, Runtime.ret, Runtime.any, Runtime.both, Runtime.either,
    Runtime.negate, Runtime.eqv, Runtime.field, Runtime.call, Runtime.v, Runtime.n,
    Runtime.completedTime, Runtime.raiseField, Runtime.lt, Runtime.pointerCheck, Runtime.out,
    Expr.nullPointer, executionInterface, objectConstants]

theorem parameters_bound (literals : CLiteralAddresses) (handle event terminate : Option Address) (flag : Bool) :
    @CCalls.parameters (cInterface literals) signature.parameters (arguments handle event terminate flag) =
      some (parameters handle event terminate flag) := by
  cases flag <;>
    simp [signature, arguments, CCalls.parameters, CCalls.parameterType,
      CBody.cast, convert, Value.truth, boolean, CBody.bind]
  all_goals
    funext name
    simp only [parameters, CBody.bind, boolean]
    split_ifs <;> simp_all

theorem call_behaviors {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p event terminate : Address)
      (flag : Bool) (clock : Time.Clock),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      load heap (p.member "kind") = some (.integer 0) →
      load heap (p.member "mode") = some (.integer 3) →
      HistoryProofs.Stored heap p clock →
      HistoryBodies.BoolWritable heap event → HistoryBodies.BoolWritable heap terminate →
      event.block ≠ p.block → terminate.block ≠ p.block →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling signature.name (arguments (some p) (some event) (some terminate) flag) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, HistoryBodies.completedHeap heap p event terminate clock⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program heap p event terminate flag clock defined hk hm stored he ht hne hnt behavior
  obtain ⟨n, executed⟩ := CBody.run_of_reaches (interface := cInterface literals)
    (HistoryBodies.completed_reaches (static := ⟨literals⟩) model signature rfl heap p event terminate flag clock
      stored hk hm he ht hne hnt)
  have agreement := body_run_agreement (cInterface literals) (executionInterface objects literals)
    (StaticInitialization.interface_types objects literals) rfl n
    (.running (Runtime.body model signature) (HistoryBodies.completedParameters p event terminate flag) heap)
    (body_agrees model objects literals)
  have bound := (parameters_agreement (cInterface literals) (executionInterface objects literals)
    (StaticInitialization.interface_types objects literals) signature.parameters
    (arguments (some p) (some event) (some terminate) flag)).symm.trans
      (parameters_bound literals (some p) (some event) (some terminate) flag)
  exact CCalls.Events.body_call_behaviors program (Runtime.function model signature) _ _ heap _ (.integer 0) n
    defined bound (BodyEmbedding.body_closed model signature) (agreement.symm.trans executed) rfl behavior

theorem null_behaviors {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (event terminate : Option Address) (flag : Bool),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling signature.name (arguments none event terminate flag) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program heap event terminate flag defined
  apply StaticInitialization.null_call objects literals program (Runtime.function model signature)
    (Runtime.modeGuard .completedStep :: Runtime.pointerCheck ["enterEventMode", "terminateSimulation"] :: tail)
    (arguments none event terminate flag) (parameters none event terminate flag) heap defined
    (parameters_bound literals _ _ _ _)
    (by simp [Runtime.function, body, Runtime.require, List.append_assoc]) rfl
    (BodyEmbedding.body_closed model signature) (body_agrees model objects literals)
  all_goals simp [parameters]

inductive Failure where | lifecycle | output
  deriving DecidableEq

def FailureCondition (reason : Failure) (kind : Kind) (mode : Mode) (event terminate : Option Address) : Prop :=
  match reason with
  | .lifecycle => ¬ Reference.Allowed .completedStep kind mode
  | .output => Reference.Allowed .completedStep kind mode ∧ (event = none ∨ terminate = none)

def message : Failure → String
  | .lifecycle => ErrorCalls.rejectionMessage
  | .output => "Missing output pointer"

theorem query_cases (handle event terminate : Option Address) (kind : Kind) (mode : Mode) :
    handle = none ∨ ∃ p, handle = some p ∧
      ((Reference.Allowed .completedStep kind mode ∧ event.isSome = true ∧ terminate.isSome = true) ∨
        ∃ reason, FailureCondition reason kind mode event terminate) := by
  classical
  cases handle with
  | none => exact Or.inl rfl
  | some p =>
    refine Or.inr ⟨p, rfl, ?_⟩
    by_cases allowed : Reference.Allowed .completedStep kind mode
    · cases event <;> cases terminate
      · exact Or.inr ⟨.output, allowed, Or.inl rfl⟩
      · exact Or.inr ⟨.output, allowed, Or.inl rfl⟩
      · exact Or.inr ⟨.output, allowed, Or.inr rfl⟩
      · exact Or.inl ⟨allowed, rfl, rfl⟩
    · exact Or.inr ⟨.lifecycle, allowed⟩

theorem lifecycle_prefix (model : Solve.FMI3Model source) (literals : CLiteralAddresses)
    (heap : Heap) (p : Address) (event terminate : Option Address) (flag : Bool) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (denied : ¬ Reference.Allowed .completedStep kind mode) :
    @GuardedCalls.FailurePrefix (cInterface literals) (Runtime.function model signature)
      (arguments (some p) event terminate flag) heap p ErrorCalls.rejectionMessage heap := by
  letI : CInterface := cInterface literals
  have reached := LifecycleGuard.reject_prefix (static := ⟨literals⟩) (parameters (some p) event terminate flag) heap p
    .completedStep kind mode (Runtime.pointerCheck ["enterEventMode", "terminateSimulation"] :: tail)
    (by simp [parameters]) (by simp [parameters]) hk hm denied
  refine ⟨rfl, BodyEmbedding.body_closed model signature, parameters (some p) event terminate flag,
    CBody.bind (parameters (some p) event terminate flag) "m" (.pointer (some p)),
    Runtime.pointerCheck ["enterEventMode", "terminateSimulation"] :: tail, 3,
    parameters_bound literals _ _ _ _, ?_, ?_, ?_⟩
  · simpa only [Runtime.function, body] using reached
  · simp [parameters, CBody.bind]
  · simp [CBody.bind, CBody.resolve]

theorem output_prefix (model : Solve.FMI3Model source) (literals : CLiteralAddresses)
    (heap : Heap) (p : Address) (event terminate : Option Address) (flag : Bool)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer 3))
    (missing : event = none ∨ terminate = none) :
    @GuardedCalls.FailurePrefix (cInterface literals) (Runtime.function model signature)
      (arguments (some p) event terminate flag) heap p "Missing output pointer" heap := by
  letI : CInterface := cInterface literals
  have entered := LifecycleGuard.accept (static := ⟨literals⟩) (parameters (some p) event terminate flag) heap p
    .completedStep .me .continuous (Runtime.pointerCheck ["enterEventMode", "terminateSimulation"] :: tail)
    (by simp [parameters]) (by simp [parameters]) hk hm ⟨rfl, rfl⟩
  refine ⟨rfl, BodyEmbedding.body_closed model signature, parameters (some p) event terminate flag,
    CBody.bind (parameters (some p) event terminate flag) "m" (.pointer (some p)),
    tail, 4, parameters_bound literals _ _ _ _, ?_, ?_, ?_⟩
  · change run (3 + 1) (.running (Runtime.body model signature) (parameters (some p) event terminate flag) heap) = _
    rw [body, run_add, entered]
    cases event <;> cases terminate <;>
      simp_all only [Option.some_ne_none, or_self, or_true, true_or]
    all_goals
      simp [run, next, Runtime.pointerCheck, Runtime.reject, Runtime.any, Runtime.negate, Runtime.either,
        Runtime.branch, Runtime.v, parameters, CBody.bind, CBody.resolve, eval, Value.truth, boolean]
  · simp [parameters, CBody.bind]
  · simp [CBody.bind, CBody.resolve]

theorem failure_prefix (model : Solve.FMI3Model source) (literals : CLiteralAddresses)
    (heap : Heap) (p : Address) (event terminate : Option Address) (flag : Bool) (kind : Kind) (mode : Mode)
    (reason : Failure)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (condition : FailureCondition reason kind mode event terminate) :
    @GuardedCalls.FailurePrefix (cInterface literals) (Runtime.function model signature)
      (arguments (some p) event terminate flag) heap p (message reason) heap := by
  cases reason with
  | lifecycle => exact lifecycle_prefix model literals heap p event terminate flag kind mode hk hm condition
  | output =>
    obtain ⟨⟨rfl, rfl⟩, missing⟩ := condition
    exact output_prefix model literals heap p event terminate flag hk hm missing

open CLiteral CCalls.Events

structure QuietContract [interface : CInterface] (program : CCalls.Events.Program E) : Prop where
  successful : ∀ (heap : Heap) (p event terminate : Address) (flag : Bool) (clock : Time.Clock),
    load heap (p.member "kind") = some (.integer 0) →
    load heap (p.member "mode") = some (.integer 3) →
    HistoryProofs.Stored heap p clock →
    HistoryBodies.BoolWritable heap event → HistoryBodies.BoolWritable heap terminate →
    event.block ≠ p.block → terminate.block ≠ p.block →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) (some event) (some terminate) flag) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, HistoryBodies.completedHeap heap p event terminate clock⟩
  null : ∀ heap event terminate flag behavior, (CCalls.Events.machine program).Behaves
    (.calling signature.name (arguments none event terminate flag) heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 3, heap⟩

def SuppressedContract [interface : CInterface] (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ (p : Address) (event terminate : Option Address) (flag : Bool) (kind : Kind) (mode : Mode)
     (reason : Failure) (logger : Option Address) (logging : Bool),
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    FailureCondition reason kind mode event terminate →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (boolean logging) →
    (logger = none ∨ logging = false) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) event terminate flag) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

def LoggedContract [interface : CInterface] (program : CCalls.Events.Program Invocation)
    (category : Address) (messages : Failure → Address) (heap : Heap) (signed : Bool) : Prop :=
  ∀ (p logger : Address) (environment : Option Address) (event terminate : Option Address) (flag : Bool) (kind : Kind)
    (mode : Mode)   (reason : Failure)
    (name : String) (effect : ReturningEffect (Logging.signature name)),
    program.addresses logger = some name →
    program.externals name = some (External.observed (Logging.signature name) effect) →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    FailureCondition reason kind mode event terminate →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) event terminate flag) heap .done) behavior ↔
      (∃ value after, effect.execute (Logging.arguments environment category (messages reason))
        (LifecycleBodies.writeMode heap p .terminated) value after ∧
        behavior = .terminates [⟨name, Logging.arguments environment category (messages reason)⟩] ⟨.integer 3, after⟩) ∨
      ((∀ value after, ¬ effect.execute (Logging.arguments environment category (messages reason))
        (LifecycleBodies.writeMode heap p .terminated) value after) ∧ behavior = .wrong [])) ∧
    (∀ value after, effect.execute (Logging.arguments environment category (messages reason))
      (LifecycleBodies.writeMode heap p .terminated) value after →
      Stored signed after category "logStatus" ∧ Stored signed after (messages reason) (message reason))

theorem quiet_correct {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      QuietContract program := by
  letI : CInterface := executionInterface objects literals
  intro program defined
  exact ⟨fun heap p event terminate flag clock =>
    call_behaviors objects literals model program heap p event terminate flag clock defined,
    fun heap event terminate flag => null_behaviors objects literals model program heap event terminate flag defined⟩

theorem suppressed_correct {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (messages : Failure → Address) (heap : Heap),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      (∀ reason, literals (message reason) = some (messages reason)) → SuppressedContract program heap := by
  letI : CInterface := executionInterface objects literals
  intro program messages heap defined helper messageBound p event terminate flag kind mode reason logger logging
    hk hm condition hl hg suppressed behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  exact StaticErrors.failure_suppressed_behaviors objects literals program (Runtime.function model signature)
    (arguments (some p) event terminate flag) heap heap p (messages reason) (message reason) _ logger logging
    (body_agrees model objects literals)
    (failure_prefix model literals heap p event terminate flag kind mode reason hk modeLoaded condition)
    defined helper (messageBound reason) hm hl hg suppressed behavior

theorem logged_correct (objects : Objects) (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program Invocation) (category : Address) (messages : Failure → Address)
      (heap : Heap) (signed : Bool),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "logStatus" = some category →
      (∀ reason, literals (message reason) = some (messages reason)) →
      Stored signed heap category "logStatus" →
      (∀ reason, Stored signed heap (messages reason) (message reason)) →
      LoggedContract program category messages heap signed := by
  letI : CInterface := executionInterface objects literals
  intro program category messages heap signed defined helper categoryBound messageBound categoryStored messageStored
    p logger environment event terminate flag kind mode reason name effect address external hk hm condition hl hg he
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have all := StaticErrors.failure_all_behaviors objects literals program (Runtime.function model signature)
    (arguments (some p) event terminate flag) heap heap p (messages reason) category logger (message reason) name environment _
    (External.observed (Logging.signature name) effect) (body_agrees model objects literals)
    (failure_prefix model literals heap p event terminate flag kind mode reason hk modeLoaded condition)
    defined helper (messageBound reason) address external rfl categoryBound hm hl hg he
  constructor
  · intro behavior
    exact (all behavior).trans (observed_choices effect _ _ (fun _ after => ⟨.integer 3, after⟩) behavior)
  · intro value after executed
    have successful := (all (.terminates [⟨name, Logging.arguments environment category (messages reason)⟩]
      ⟨.integer 3, after⟩)).mpr (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := CCalls.Events.termination_preserves successful
    exact ⟨categoryStored.preserved preserved, (messageStored reason).preserved preserved⟩

theorem failure_unique (first : FailureCondition a kind mode event terminate)
    (second : FailureCondition b kind mode event terminate) : a = b := by
  cases a <;> cases b <;> simp_all [FailureCondition]

end Rumoca.FMI3.CompletedCalls
