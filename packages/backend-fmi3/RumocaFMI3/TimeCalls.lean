import RumocaFMI3.StaticErrorCalls
import RumocaFMI3.LoggingContract
import RumocaFMI3.TimeProofs

/-! Complete ME time calls in the static object interface, with
independent time admission and all represented error/logging cases. -/
noncomputable section
namespace Rumoca.FMI3.TimeCalls
open CTree CMemory CBody StaticFactory CLiteral.Interface
open Binary64 (toBits)

def signature : Signature := ⟨"fmi3Status", "fmi3SetTime",
  [⟨"fmi3Instance", "instance", false⟩, ⟨"fmi3Float64", "time", false⟩]⟩

def arguments (handle : Option Address) (bits : BitVec 64) : List Value :=
  [.pointer handle, .float64 bits]

def parameters (handle : Option Address) (bits : BitVec 64) : Locals :=
  CBody.bind (CBody.bind (fun _ => none) "time" (.float64 bits)) "instance" (.pointer handle)

def message : String := "Time is outside the permitted interval"

def tail : List Stmt := [Runtime.put "time" (Runtime.v "time"), Runtime.ok]

theorem body (model : Solve.FMI3Model source) :
    Runtime.body model signature = Runtime.require .setTime ++ Runtime.reject Runtime.invalidTime message :: tail := by
  simp [Runtime.body, signature, message, tail]

theorem body_agrees (model : Solve.FMI3Model source) (objects : Objects) (literals : CLiteralAddresses) :
    CodeAgrees (cInterface literals) (executionInterface objects literals) (Runtime.body model signature) := by
  rw [body]
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, tail, Runtime.require, Runtime.instancePrefix,
    Runtime.modeGuard, Runtime.allowedExpression, permittedModes, Runtime.put, Runtime.invalidTime,
    Runtime.mode, Runtime.ok, Runtime.reject, Runtime.fail,
    Runtime.branch, Runtime.ret, Runtime.any, Runtime.both, Runtime.either,
    Runtime.negate, Runtime.eqv, Runtime.field, Runtime.finite, Runtime.lt, Runtime.gt,
    Runtime.call, Runtime.v, Runtime.n, Expr.nullPointer, executionInterface, objectConstants]

theorem finite_parameters (p : Address) (bits : BitVec 64) :
    parameters (some p) bits = TimeProofs.parameters p bits := by
  funext name
  simp [parameters, TimeProofs.parameters, CBody.bind]

theorem parameters_bound (literals : CLiteralAddresses) (handle : Option Address) (bits : BitVec 64) :
    @CCalls.parameters (cInterface literals) signature.parameters (arguments handle bits) =
      some (parameters handle bits) := by
  simp [signature, arguments, CCalls.parameters, CCalls.parameterType, parameters,
    CBody.cast, convert, CBody.bind]

/-- The reference history and optional stop have their own heap representation. -/
structure Bounds (heap : Heap) (p : Address) (window : Time.Window) (minimum : Binary64.Value) : Prop where
  lower : window.RepresentsLower minimum
  minimumValue : load heap (p.member "timeMin") = some (.finite minimum)
  stopDefined : load heap (p.member "stopDefined") = some (boolean window.stopTime.isSome)
  stopValue : ∀ stop, window.stopTime = some stop → load heap (p.member "stop") = some (.finite stop)

def Admitted (window : Time.Window) (bits : BitVec 64) : Prop :=
  ∃ time : Binary64.Value, bits = (toBits time).val ∧ window.Admissible time

inductive Failure where | lifecycle | nonfinite | window
  deriving DecidableEq

def failureMessage : Failure → String
  | .lifecycle => ErrorCalls.rejectionMessage
  | .nonfinite | .window => message

def FailureCondition (reason : Failure) (kind : Kind) (mode : Mode)
    (window : Time.Window) (bits : BitVec 64) : Prop :=
  match reason with
  | .lifecycle => ¬ Reference.Allowed .setTime kind mode
  | .nonfinite => Reference.Allowed .setTime kind mode ∧
      ¬ ∃ time : Binary64.Value, bits = (toBits time).val
  | .window => Reference.Allowed .setTime kind mode ∧
      ∃ time : Binary64.Value, bits = (toBits time).val ∧ ¬ window.Admissible time

theorem bit_cases (bits : BitVec 64) :
    (∃ time : Binary64.Value, bits = (toBits time).val) ∨
      (Value.float64 bits).isFinite = some false := by
  by_cases finite : bits.toNat % Binary64.signPlace < Binary64.magnitudeCount
  · exact Or.inl ⟨Binary64.ofBits ⟨bits, finite⟩,
      (congrArg Subtype.val (Binary64.toBits_ofBits ⟨bits, finite⟩)).symm⟩
  · exact Or.inr (by simp [Value.isFinite, finite])

theorem query_cases (handle : Option Address) (kind : Kind) (mode : Mode)
    (window : Time.Window) (bits : BitVec 64) :
    handle = none ∨ ∃ p, handle = some p ∧
      ((Reference.Allowed .setTime kind mode ∧ Admitted window bits) ∨
        ∃ reason, FailureCondition reason kind mode window bits) := by
  classical
  cases handle with
  | none => exact Or.inl rfl
  | some p =>
    refine Or.inr ⟨p, rfl, ?_⟩
    by_cases allowed : Reference.Allowed .setTime kind mode
    · by_cases finite : ∃ time : Binary64.Value, bits = (toBits time).val
      · obtain ⟨time, encoded⟩ := finite
        by_cases admissible : window.Admissible time
        · exact Or.inl ⟨allowed, time, encoded, admissible⟩
        · exact Or.inr ⟨.window, allowed, time, encoded, admissible⟩
      · exact Or.inr ⟨.nonfinite, allowed, finite⟩
    · exact Or.inr ⟨.lifecycle, allowed⟩

theorem failure_unique (first : FailureCondition a kind mode window bits)
    (second : FailureCondition b kind mode window bits) : a = b := by
  cases a <;> cases b <;> simp_all [FailureCondition]

theorem call_behaviors {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
      (window : Time.Window) (minimum time : Binary64.Value) (old : Option Value),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      load heap (p.member "kind") = some (.integer 0) →
      load heap (p.member "mode") = some (.integer 3) →
      Bounds heap p window minimum →
      heap (p.member "time") = some ⟨.float64, true, old⟩ → window.Admissible time →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling signature.name (arguments (some p) (toBits time).val) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, StateProofs.written heap (p.member "time") (toBits time).val⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program heap p window minimum time old defined hk hm bounds writable admissible behavior
  have executed := TimeProofs.set_run (static := ⟨literals⟩) model signature rfl heap p window minimum time old
    hk hm bounds.lower bounds.minimumValue bounds.stopDefined bounds.stopValue writable admissible
  have agreement := body_run_agreement (cInterface literals) (executionInterface objects literals)
    (StaticInitialization.interface_types objects literals) rfl 6
    (.running (Runtime.body model signature) (TimeProofs.parameters p (toBits time).val) heap)
    (body_agrees model objects literals)
  have parameterValues := (parameters_agreement (cInterface literals) (executionInterface objects literals)
    (StaticInitialization.interface_types objects literals) signature.parameters
    (arguments (some p) (toBits time).val)).symm.trans (parameters_bound literals _ _)
  rw [finite_parameters] at parameterValues
  exact CCalls.Events.body_call_behaviors program (Runtime.function model signature) _ _ heap _ (.integer 0) 6
    defined parameterValues (BodyEmbedding.body_closed model signature) (agreement.symm.trans executed) rfl behavior

theorem null_behaviors {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (bits : BitVec 64),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling signature.name (arguments none bits) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program heap bits defined
  apply StaticInitialization.null_call objects literals program (Runtime.function model signature)
    (Runtime.modeGuard .setTime :: Runtime.reject Runtime.invalidTime message :: tail)
    (arguments none bits) (parameters none bits) heap defined (parameters_bound literals _ _)
    (by simp [Runtime.function, body, Runtime.require, List.append_assoc]) rfl
    (BodyEmbedding.body_closed model signature) (body_agrees model objects literals)
  all_goals simp [parameters, CBody.bind]

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem lifecycle_prefix (model : Solve.FMI3Model source) (heap : Heap) (p : Address)
    (bits : BitVec 64) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (denied : ¬ Reference.Allowed .setTime kind mode) :
    GuardedCalls.FailurePrefix (Runtime.function model signature)
      (arguments (some p) bits) heap p ErrorCalls.rejectionMessage heap := by
  have reached := LifecycleGuard.reject_prefix (TimeProofs.parameters p bits) heap p
    .setTime kind mode (Runtime.reject Runtime.invalidTime message :: tail)
    (by simp [TimeProofs.parameters]) (by simp [TimeProofs.parameters]) hk hm denied
  refine ⟨rfl, BodyEmbedding.body_closed model signature, TimeProofs.parameters p bits,
    TimeProofs.locals p bits, Runtime.reject Runtime.invalidTime message :: tail, 3,
    ?_, ?_, ?_, ?_⟩
  · simpa only [finite_parameters] using parameters_bound static.addresses (some p) bits
  · simpa only [Runtime.function, body, TimeProofs.locals] using reached
  · simp [TimeProofs.locals, TimeProofs.parameters, CBody.bind]
  · simp [TimeProofs.locals, CBody.bind, CBody.resolve]

private theorem invalid_prefix (model : Solve.FMI3Model source) (heap : Heap) (p : Address)
    (bits : BitVec 64)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer 3))
    (rejected : eval (TimeProofs.locals p bits) heap Runtime.invalidTime = some (boolean true)) :
    GuardedCalls.FailurePrefix (Runtime.function model signature)
      (arguments (some p) bits) heap p message heap := by
  have entered := LifecycleGuard.accept (TimeProofs.parameters p bits) heap p
    .setTime .me .continuous (Runtime.reject Runtime.invalidTime message :: tail)
    (by simp [TimeProofs.parameters]) (by simp [TimeProofs.parameters]) hk hm ⟨rfl, rfl⟩
  refine ⟨rfl, BodyEmbedding.body_closed model signature, TimeProofs.parameters p bits,
    TimeProofs.locals p bits, tail, 4, ?_, ?_, ?_, ?_⟩
  · simpa only [finite_parameters] using parameters_bound static.addresses (some p) bits
  · change run (3 + 1) (.running (Runtime.body model signature) (TimeProofs.parameters p bits) heap) = _
    rw [body, run_add, entered]
    simp only [Option.bind_some]
    change run 1 (.running (Runtime.reject Runtime.invalidTime message :: tail) (TimeProofs.locals p bits) heap) = _
    simp [run, next, Runtime.reject, Runtime.branch, rejected, boolean, Value.truth]
  · simp [TimeProofs.locals, TimeProofs.parameters, CBody.bind]
  · simp [TimeProofs.locals, CBody.bind, CBody.resolve]

/-- A nonfinite argument fails before reading any history or experiment bound. -/
theorem nonfinite_prefix (model : Solve.FMI3Model source) (heap : Heap) (p : Address)
    (bits : BitVec 64)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer 3))
    (nonfinite : ¬ ∃ time : Binary64.Value, bits = (toBits time).val) :
    GuardedCalls.FailurePrefix (Runtime.function model signature)
      (arguments (some p) bits) heap p message heap := by
  exact invalid_prefix model heap p bits hk hm
    (TimeProofs.guard_nonfinite heap p bits ((bit_cases bits).resolve_left nonfinite))

set_option maxRecDepth 10000 in
theorem window_rejected_eval (heap : Heap) (p : Address) (window : Time.Window)
    (minimum time : Binary64.Value) (bounds : Bounds heap p window minimum)
    (invalid : ¬ window.Admissible time) :
    eval (TimeProofs.locals p (toBits time).val) heap Runtime.invalidTime = some (boolean true) := by
  have rejects : TimeProofs.rejects minimum window.stopTime time = true :=
    Bool.eq_true_of_not_eq_false (fun accepted => invalid ((TimeProofs.rejects_iff window minimum time bounds.lower).mp accepted))
  have finite := Value.isFinite_finite time
  change Value.isFinite (.float64 (toBits time).val) = some true at finite
  obtain ⟨_, minimumValue, stopDefined, stopValue⟩ := bounds
  cases stop : window.stopTime with
  | none =>
    cases lower : Rumoca.Float64.test .lt (toBits time).val (toBits minimum).val <;>
      simp_all [Runtime.invalidTime, Runtime.any, Runtime.either, Runtime.both, Runtime.negate,
        Runtime.finite, Runtime.call, Runtime.lt, Runtime.gt, Runtime.field, Runtime.v,
        eval, TimeProofs.locals, TimeProofs.parameters, CBody.bind, CBody.resolve, constants, Value.address,
        comparison, floatComparison, Value.finite, TimeProofs.rejects, Runtime.n, Value.truth, boolean]
  | some bound =>
    have stored := stopValue bound stop
    cases lower : Rumoca.Float64.test .lt (toBits time).val (toBits minimum).val <;>
      cases upper : Rumoca.Float64.test .gt (toBits time).val (toBits bound).val <;>
      simp_all [Runtime.invalidTime, Runtime.any, Runtime.either, Runtime.both, Runtime.negate,
        Runtime.finite, Runtime.call, Runtime.lt, Runtime.gt, Runtime.field, Runtime.v,
        eval, TimeProofs.locals, TimeProofs.parameters, CBody.bind, CBody.resolve, constants, Value.address,
        comparison, floatComparison, Value.finite, TimeProofs.rejects, Runtime.n, Value.truth, boolean]

theorem failure_prefix (model : Solve.FMI3Model source) (heap : Heap) (p : Address)
    (bits : BitVec 64) (kind : Kind) (mode : Mode) (window : Time.Window)
    (minimum : Binary64.Value) (reason : Failure)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (bounds : reason = .window → Bounds heap p window minimum)
    (condition : FailureCondition reason kind mode window bits) :
    GuardedCalls.FailurePrefix (Runtime.function model signature)
      (arguments (some p) bits) heap p (failureMessage reason) heap := by
  cases reason with
  | lifecycle => exact lifecycle_prefix model heap p bits kind mode hk hm condition
  | nonfinite =>
    obtain ⟨⟨rfl, rfl⟩, nonfinite⟩ := condition
    exact nonfinite_prefix model heap p bits hk hm nonfinite
  | window =>
    obtain ⟨⟨rfl, rfl⟩, time, rfl, invalid⟩ := condition
    exact invalid_prefix model heap p (toBits time).val hk hm
      (window_rejected_eval heap p window minimum time (bounds rfl) invalid)


end

open CLiteral CCalls.Events

structure QuietContract [interface : CInterface] (program : CCalls.Events.Program E) : Prop where
  successful : ∀ (heap : Heap) (p : Address) (window : Time.Window)
    (minimum time : Binary64.Value) (old : Option Value),
    load heap (p.member "kind") = some (.integer 0) →
    load heap (p.member "mode") = some (.integer 3) →
    Bounds heap p window minimum → heap (p.member "time") = some ⟨.float64, true, old⟩ →
    window.Admissible time →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) (toBits time).val) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, StateProofs.written heap (p.member "time") (toBits time).val⟩
  null : ∀ heap bits behavior, (CCalls.Events.machine program).Behaves
    (.calling signature.name (arguments none bits) heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 3, heap⟩

def SuppressedContract [interface : CInterface] (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ (p : Address) (bits : BitVec 64) (kind : Kind) (mode : Mode) (window : Time.Window)
    (minimum : Binary64.Value) (reason : Failure) (logger : Option Address) (logging : Bool),
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    (reason = .window → Bounds heap p window minimum) →
    FailureCondition reason kind mode window bits →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (boolean logging) →
    (logger = none ∨ logging = false) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) bits) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

def LoggedContract [interface : CInterface] (program : CCalls.Events.Program Invocation)
    (category : Address) (messages : Failure → Address) (heap : Heap) (signed : Bool) : Prop :=
  ∀ (p logger : Address) (environment : Option Address) (bits : BitVec 64) (kind : Kind)
    (mode : Mode) (window : Time.Window) (minimum : Binary64.Value) (reason : Failure)
    (name : String) (effect : ReturningEffect (Logging.signature name)),
    program.addresses logger = some name →
    program.externals name = some (External.observed (Logging.signature name) effect) →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    (reason = .window → Bounds heap p window minimum) →
    FailureCondition reason kind mode window bits →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) bits) heap .done) behavior ↔
      (∃ value after, effect.execute (Logging.arguments environment category (messages reason))
        (LifecycleBodies.writeMode heap p .terminated) value after ∧
        behavior = .terminates [⟨name, Logging.arguments environment category (messages reason)⟩] ⟨.integer 3, after⟩) ∨
      ((∀ value after, ¬ effect.execute (Logging.arguments environment category (messages reason))
        (LifecycleBodies.writeMode heap p .terminated) value after) ∧ behavior = .wrong [])) ∧
    (∀ value after, effect.execute (Logging.arguments environment category (messages reason))
      (LifecycleBodies.writeMode heap p .terminated) value after →
      Stored signed after category "logStatus" ∧ Stored signed after (messages reason) (failureMessage reason))

theorem quiet_correct {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      QuietContract program := by
  letI : CInterface := executionInterface objects literals
  intro program defined
  exact ⟨fun heap p window minimum time old =>
    call_behaviors objects literals model program heap p window minimum time old defined,
    fun heap bits => null_behaviors objects literals model program heap bits defined⟩

theorem suppressed_correct {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (messages : Failure → Address) (heap : Heap),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      (∀ reason, literals (failureMessage reason) = some (messages reason)) → SuppressedContract program heap := by
  letI : CInterface := executionInterface objects literals
  intro program messages heap defined helper messageBound p bits kind mode window minimum reason logger logging
    hk hm bounds condition hl hg suppressed behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  exact StaticErrors.failure_suppressed_behaviors (ErrorContext.static objects literals) program (Runtime.function model signature)
    (arguments (some p) bits) heap heap p (messages reason) (failureMessage reason) _ logger logging
    (body_agrees model objects literals)
    (failure_prefix (static := ⟨literals⟩) model heap p bits kind mode window minimum reason hk modeLoaded bounds condition)
    defined helper (messageBound reason) hm hl hg suppressed behavior

theorem logged_correct (objects : Objects) (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program Invocation) (category : Address) (messages : Failure → Address)
      (heap : Heap) (signed : Bool),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "logStatus" = some category →
      (∀ reason, literals (failureMessage reason) = some (messages reason)) →
      Stored signed heap category "logStatus" →
      (∀ reason, Stored signed heap (messages reason) (failureMessage reason)) →
      LoggedContract program category messages heap signed := by
  letI : CInterface := executionInterface objects literals
  intro program category messages heap signed defined helper categoryBound messageBound categoryStored messageStored
    p logger environment bits kind mode window minimum reason name effect address external hk hm bounds condition hl hg he
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have all := StaticErrors.failure_all_behaviors (ErrorContext.static objects literals) program (Runtime.function model signature)
    (arguments (some p) bits) heap heap p (messages reason) category logger (failureMessage reason) name environment _
    (External.observed (Logging.signature name) effect) (body_agrees model objects literals)
    (failure_prefix (static := ⟨literals⟩) model heap p bits kind mode window minimum reason hk modeLoaded bounds condition)
    defined helper (messageBound reason) address external rfl categoryBound hm hl hg he
  constructor
  · intro behavior
    exact (all behavior).trans (observed_choices effect _ _ (fun _ after => ⟨.integer 3, after⟩) behavior)
  · intro value after executed
    have successful := (all (.terminates [⟨name, Logging.arguments environment category (messages reason)⟩]
      ⟨.integer 3, after⟩)).mpr (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := CCalls.Events.termination_preserves successful
    exact ⟨categoryStored.preserved preserved, (messageStored reason).preserved preserved⟩

theorem admitted_finite (window : Time.Window) (time : Binary64.Value) :
    Admitted window (toBits time).val ↔ window.Admissible time := by
  constructor
  · rintro ⟨other, encoded, admissible⟩
    have same : time = other := Binary64.finiteEncodingEquiv.injective (Subtype.ext encoded)
    simpa only [same] using admissible
  · intro admissible
    exact ⟨time, rfl, admissible⟩

/-- A rejected reason cannot also describe an accepted call. Encoding's
bijection retains exact finite bits, including both signed zeros. -/
theorem failure_excludes_success (failure : FailureCondition reason kind mode window bits) :
    ¬ (Reference.Allowed .setTime kind mode ∧ Admitted window bits) := by
  intro accepted
  cases reason with
  | lifecycle => exact failure accepted.1
  | nonfinite => exact failure.2 ⟨accepted.2.choose, accepted.2.choose_spec.1⟩
  | window =>
    obtain ⟨_, time, rfl, invalid⟩ := failure
    exact invalid ((admitted_finite window time).mp accepted.2)

end Rumoca.FMI3.TimeCalls
