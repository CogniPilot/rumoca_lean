import RumocaC.OutputAssignments
import RumocaC.PointerConditions
import RumocaFMI3.TerminationContract
import RumocaFMI3.TimeContract

noncomputable section
namespace Rumoca.FMI3.DiscreteCalls
open CTree CMemory CBody StaticFactory CLiteral.Interface

def layouts : List (String × CType) :=
  [("discreteStatesNeedUpdate", .boolean), ("terminateSimulation", .boolean),
   ("nominalsOfContinuousStatesChanged", .boolean), ("valuesOfContinuousStatesChanged", .boolean),
   ("nextEventTimeDefined", .boolean), ("nextEventTime", .float64)]

def names : List String := layouts.map Prod.fst

def signature : Signature := ⟨"fmi3Status", "fmi3UpdateDiscreteStates",
  [⟨"fmi3Instance", "instance", false⟩,
   ⟨"fmi3Boolean *", "discreteStatesNeedUpdate", false⟩,
   ⟨"fmi3Boolean *", "terminateSimulation", false⟩,
   ⟨"fmi3Boolean *", "nominalsOfContinuousStatesChanged", false⟩,
   ⟨"fmi3Boolean *", "valuesOfContinuousStatesChanged", false⟩,
   ⟨"fmi3Boolean *", "nextEventTimeDefined", false⟩,
   ⟨"fmi3Float64 *", "nextEventTime", false⟩]⟩

def arguments (handle : Option Address) (addresses : String → Option Address) : List Value :=
  .pointer handle :: names.map (fun name => .pointer (addresses name))

def parameters (handle : Option Address) (addresses : String → Option Address) : Locals := fun name =>
  if name = "instance" then some (.pointer handle)
  else if name ∈ names then some (.pointer (addresses name)) else none

def zeroValue (type : CType) : Value :=
  if type = .float64 then .finite Binary64.positiveZero else .integer 0

def output (addresses : String → Address) (layout : String × CType) : COutputAssignments.Entry :=
  ⟨layout.1, addresses layout.1, layout.2, .nat 0, .integer 0, zeroValue layout.2⟩

def outputs (addresses : String → Address) : List COutputAssignments.Entry := layouts.map (output addresses)

def tail : List Stmt := names.map (fun name => Runtime.out name (Runtime.n 0)) ++ [Runtime.ok]

theorem body (model : Solve.FMI3Model source) :
    Runtime.body model signature = Runtime.require .updateDiscrete ++ Runtime.pointerCheck names :: tail := by
  simp [Runtime.body, signature, names, layouts, tail]

theorem tail_outputs (addresses : String → Address) :
    tail = (outputs addresses).map COutputAssignments.statement ++ [Runtime.ok] := rfl

theorem body_agrees (model : Solve.FMI3Model source) (objects : Objects) (literals : CLiteralAddresses) :
    CodeAgrees (cInterface literals) (executionInterface objects literals) (Runtime.body model signature) := by
  rw [body]
  simp [CodeAgrees, StmtAgrees, ExprAgrees, CLiteral.Interface.names, tail, names, layouts,
    Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression,
    permittedModes, Runtime.mode, Runtime.ok, Runtime.reject,
    Runtime.fail, Runtime.branch, Runtime.ret, Runtime.any, Runtime.both, Runtime.either,
    Runtime.negate, Runtime.eqv, Runtime.field, Runtime.call, Runtime.v, Runtime.n,
    Runtime.pointerCheck, Runtime.out, Expr.nullPointer, executionInterface, objectConstants]

theorem parameters_bound (literals : CLiteralAddresses) (handle : Option Address)
    (addresses : String → Option Address) :
    @CCalls.parameters (cInterface literals) signature.parameters (arguments handle addresses) =
      some (parameters handle addresses) := by
  simp [signature, arguments, names, layouts, CCalls.parameters, CCalls.parameterType,
    CBody.cast, convert, CBody.bind]
  funext name
  simp only [parameters, names, layouts, List.map, List.mem_cons, List.not_mem_nil, or_false, CBody.bind]
  split_ifs <;> simp_all

theorem output_bound [interface : CInterface] (handle : Option Address) (addresses : String → Option Address)
    (p : Address) (name : String) (member : name ∈ names) :
    resolve (CBody.bind (parameters handle addresses) "m" (.pointer (some p))) name =
      some (.pointer (addresses name)) := by
  simp only [names, layouts, List.map, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [resolve, parameters, names, layouts, CBody.bind]

theorem outputs_ready [interface : CInterface] (heap : Heap) (p : Address) (addresses : String → Address)
    (writable : ∀ entry ∈ outputs addresses, COutputAssignments.Writable heap entry) :
    ∀ entry ∈ outputs addresses,
      COutputAssignments.Ready
        (CBody.bind (parameters (some p) (fun name => some (addresses name))) "m" (.pointer (some p))) heap entry := by
  intro entry member
  obtain ⟨layout, declared, rfl⟩ := List.mem_map.mp member
  refine ⟨output_bound _ _ p layout.1 (List.mem_map.mpr ⟨layout, declared, rfl⟩),
    fun _ => rfl, ?_, ?_, writable _ (List.mem_map.mpr ⟨layout, declared, rfl⟩)⟩
  all_goals
    simp only [layouts, List.mem_cons, List.not_mem_nil, or_false] at declared
    rcases declared with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [output, zeroValue, convert, Value.truth]

theorem body_run (model : Solve.FMI3Model source) (literals : CLiteralAddresses)
    (heap : Heap) (p : Address) (addresses : String → Address)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer 2))
    (writable : ∀ entry ∈ outputs addresses, COutputAssignments.Writable heap entry) :
    @run (cInterface literals) 11
      (.running (Runtime.body model signature) (parameters (some p) (fun name => some (addresses name))) heap) =
      some (.returned ⟨.integer 0, COutputAssignments.after heap (outputs addresses)⟩) := by
  letI : CInterface := cInterface literals
  let args := parameters (some p) (fun name => some (addresses name))
  let env := CBody.bind args "m" (.pointer (some p))
  have entered := LifecycleGuard.accept (static := ⟨literals⟩) args heap p .updateDiscrete .me .event
    (Runtime.pointerCheck names :: tail)
    (by simp [args, parameters]) (by simp [args, parameters, names, layouts]) hk hm ⟨rfl, rfl⟩
  have checked := CPointerConditions.missing_eval env heap names (fun name => some (addresses name))
    (output_bound (some p) (fun name => some (addresses name)) p)
  have guard : run 1 (.running (Runtime.pointerCheck names :: tail) env heap) =
      some (.running tail env heap) := by
    have falseCheck : eval env heap (CPointerConditions.missing names) = some (boolean false) := by
      simpa [names, layouts] using checked
    change run 1 (.running (Runtime.reject (CPointerConditions.missing names) "Missing output pointer" :: tail) env heap) = _
    simp [run, CBody.next, CBody.nextWith, CBody.legacyExpressions, Runtime.reject, Runtime.branch, falseCheck, Value.truth, boolean]
  have written := COutputAssignments.run_all env heap (outputs addresses) [Runtime.ok]
    (outputs_ready heap p addresses writable)
  have returned := HistoryBodies.return_ok (static := ⟨literals⟩) env
    (COutputAssignments.after heap (outputs addresses)) (by simp [env, args, parameters, CBody.bind, resolve, constants, names, layouts])
  rw [body, show 11 = 3 + (1 + (6 + 1)) from rfl, run_add, entered]
  simp only [Option.bind_some]
  rw [run_add, guard]
  simp only [Option.bind_some]
  rw [tail_outputs addresses, run_add]
  change (run (outputs addresses).length
    (.running ((outputs addresses).map COutputAssignments.statement ++ [Runtime.ok]) env heap)).bind (run 1) = _
  rw [written]
  exact returned

theorem call_behaviors {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p : Address) (addresses : String → Address),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      load heap (p.member "kind") = some (.integer 0) →
      load heap (p.member "mode") = some (.integer 2) →
      (∀ entry ∈ outputs addresses, COutputAssignments.Writable heap entry) →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling signature.name (arguments (some p) (fun name => some (addresses name))) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, COutputAssignments.after heap (outputs addresses)⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program heap p addresses defined hk hm writable behavior
  have executed := body_run model literals heap p addresses hk hm writable
  have agreement := body_run_agreement (cInterface literals) (executionInterface objects literals)
    (StaticInitialization.interface_types objects literals) rfl 11
    (.running (Runtime.body model signature) (parameters (some p) (fun name => some (addresses name))) heap)
    (body_agrees model objects literals)
  have bound := (parameters_agreement (cInterface literals) (executionInterface objects literals)
    (StaticInitialization.interface_types objects literals) signature.parameters
    (arguments (some p) (fun name => some (addresses name)))).symm.trans (parameters_bound literals _ _)
  exact CCalls.Events.body_call_behaviors program (Runtime.function model signature) _ _ heap _ (.integer 0) 11
    defined bound (BodyEmbedding.body_closed model signature) (agreement.symm.trans executed) rfl behavior

theorem null_behaviors {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (addresses : String → Option Address),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling signature.name (arguments none addresses) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program heap addresses defined
  apply StaticInitialization.null_call objects literals program (Runtime.function model signature)
    (Runtime.modeGuard .updateDiscrete :: Runtime.pointerCheck names :: tail)
    (arguments none addresses) (parameters none addresses) heap defined (parameters_bound literals _ _)
    (by simp [Runtime.function, body, Runtime.require, List.append_assoc]) rfl
    (BodyEmbedding.body_closed model signature) (body_agrees model objects literals)
  all_goals simp [parameters, names, layouts]

inductive Failure where | lifecycle | output
  deriving DecidableEq

def FailureCondition (reason : Failure) (kind : Kind) (mode : Mode) (addresses : String → Option Address) : Prop :=
  match reason with
  | .lifecycle => ¬ Reference.Allowed .updateDiscrete kind mode
  | .output => Reference.Allowed .updateDiscrete kind mode ∧ ∃ name ∈ names, addresses name = none

def message : Failure → String
  | .lifecycle => ErrorCalls.rejectionMessage
  | .output => "Missing output pointer"

theorem query_cases (handle : Option Address) (addresses : String → Option Address) (kind : Kind) (mode : Mode) :
    handle = none ∨ ∃ p, handle = some p ∧
      ((Reference.Allowed .updateDiscrete kind mode ∧ ∀ name ∈ names, (addresses name).isSome = true) ∨
        ∃ reason, FailureCondition reason kind mode addresses) := by
  classical
  cases handle with
  | none => exact Or.inl rfl
  | some p =>
    refine Or.inr ⟨p, rfl, ?_⟩
    by_cases allowed : Reference.Allowed .updateDiscrete kind mode
    · by_cases missing : ∃ name ∈ names, addresses name = none
      · exact Or.inr ⟨.output, allowed, missing⟩
      · refine Or.inl ⟨allowed, ?_⟩
        intro name member
        cases selected : addresses name with
        | none => exact False.elim (missing ⟨name, member, selected⟩)
        | some => rfl
    · exact Or.inr ⟨.lifecycle, allowed⟩

theorem lifecycle_prefix (model : Solve.FMI3Model source) (literals : CLiteralAddresses)
    (heap : Heap) (p : Address) (addresses : String → Option Address) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (denied : ¬ Reference.Allowed .updateDiscrete kind mode) :
    @GuardedCalls.FailurePrefix (cInterface literals) (Runtime.function model signature)
      (arguments (some p) addresses) heap p ErrorCalls.rejectionMessage heap := by
  letI : CInterface := cInterface literals
  have reached := LifecycleGuard.reject_prefix (static := ⟨literals⟩) (parameters (some p) addresses) heap p
    .updateDiscrete kind mode (Runtime.pointerCheck names :: tail)
    (by simp [parameters]) (by simp [parameters, names, layouts]) hk hm denied
  refine ⟨rfl, BodyEmbedding.body_closed model signature, parameters (some p) addresses,
    CBody.bind (parameters (some p) addresses) "m" (.pointer (some p)),
    Runtime.pointerCheck names :: tail, 3, parameters_bound literals _ _, ?_, ?_, ?_⟩
  · simpa only [Runtime.function, body] using reached
  · simp [parameters, CBody.bind, names, layouts]
  · simp [CBody.bind, CBody.resolve]

theorem output_prefix (model : Solve.FMI3Model source) (literals : CLiteralAddresses)
    (heap : Heap) (p : Address) (addresses : String → Option Address)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer 2))
    (missing : ∃ name ∈ names, addresses name = none) :
    @GuardedCalls.FailurePrefix (cInterface literals) (Runtime.function model signature)
      (arguments (some p) addresses) heap p "Missing output pointer" heap := by
  letI : CInterface := cInterface literals
  let args := parameters (some p) addresses
  let env := CBody.bind args "m" (.pointer (some p))
  have entered := LifecycleGuard.accept (static := ⟨literals⟩) args heap p .updateDiscrete .me .event
    (Runtime.pointerCheck names :: tail)
    (by simp [args, parameters]) (by simp [args, parameters, names, layouts]) hk hm ⟨rfl, rfl⟩
  have checked := CPointerConditions.missing_eval env heap names addresses (output_bound (some p) addresses p)
  rw [(CPointerConditions.missing_iff names addresses).mpr missing] at checked
  refine ⟨rfl, BodyEmbedding.body_closed model signature, args, env,
    tail, 4, parameters_bound literals _ _, ?_, ?_, ?_⟩
  · change run (3 + 1) (.running (Runtime.body model signature) args heap) = _
    rw [body, run_add, entered]
    simp only [Option.bind_some]
    change run 1 (.running (Runtime.reject (CPointerConditions.missing names) "Missing output pointer" :: tail) env heap) = _
    simp [run, CBody.next, CBody.nextWith, CBody.legacyExpressions, Runtime.reject, Runtime.branch, checked, Value.truth, boolean]
  · simp [env, args, parameters, CBody.bind, names, layouts]
  · simp [env, CBody.bind, CBody.resolve]

theorem failure_prefix (model : Solve.FMI3Model source) (literals : CLiteralAddresses)
    (heap : Heap) (p : Address) (addresses : String → Option Address) (kind : Kind) (mode : Mode)
    (reason : Failure)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (condition : FailureCondition reason kind mode addresses) :
    @GuardedCalls.FailurePrefix (cInterface literals) (Runtime.function model signature)
      (arguments (some p) addresses) heap p (message reason) heap := by
  cases reason with
  | lifecycle => exact lifecycle_prefix model literals heap p addresses kind mode hk hm condition
  | output =>
    obtain ⟨⟨rfl, rfl⟩, missing⟩ := condition
    exact output_prefix model literals heap p addresses hk hm missing

theorem failure_unique (first : FailureCondition a kind mode addresses)
    (second : FailureCondition b kind mode addresses) : a = b := by
  cases a <;> cases b <;> simp_all [FailureCondition]

open CLiteral CCalls.Events

structure QuietContract [interface : CInterface] (program : CCalls.Events.Program E) : Prop where
  successful : ∀ (heap : Heap) (p : Address) (addresses : String → Address),
    load heap (p.member "kind") = some (.integer 0) →
    load heap (p.member "mode") = some (.integer 2) →
    (∀ entry ∈ outputs addresses, COutputAssignments.Writable heap entry) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) (fun name => some (addresses name))) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, COutputAssignments.after heap (outputs addresses)⟩
  null : ∀ heap addresses behavior, (CCalls.Events.machine program).Behaves
    (.calling signature.name (arguments none addresses) heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 3, heap⟩

def SuppressedContract [interface : CInterface] (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ (p : Address) (addresses : String → Option Address) (kind : Kind) (mode : Mode)
     (reason : Failure) (logger : Option Address) (logging : Bool),
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    FailureCondition reason kind mode addresses →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (boolean logging) →
    (logger = none ∨ logging = false) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) addresses) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

def LoggedContract [interface : CInterface] (program : CCalls.Events.Program Invocation)
    (category : Address) (messages : Failure → Address) (heap : Heap) (signed : Bool) : Prop :=
  ∀ (p logger : Address) (environment : Option Address) (addresses : String → Option Address) (kind : Kind)
    (mode : Mode)   (reason : Failure)
    (name : String) (effect : ReturningEffect (Logging.signature name)),
    program.addresses logger = some name →
    program.externals name = some (External.observed (Logging.signature name) effect) →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    FailureCondition reason kind mode addresses →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) addresses) heap .done) behavior ↔
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
  exact ⟨fun heap p addresses => call_behaviors objects literals model program heap p addresses defined,
    fun heap addresses => null_behaviors objects literals model program heap addresses defined⟩

theorem suppressed_correct {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (messages : Failure → Address) (heap : Heap),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      (∀ reason, literals (message reason) = some (messages reason)) → SuppressedContract program heap := by
  letI : CInterface := executionInterface objects literals
  intro program messages heap defined helper messageBound p addresses kind mode reason logger logging
    hk hm condition hl hg suppressed behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  exact StaticErrors.failure_suppressed_behaviors (ErrorContext.static objects literals) program (Runtime.function model signature)
    (arguments (some p) addresses) heap heap p (messages reason) (message reason) _ logger logging
    (body_agrees model objects literals)
    (failure_prefix model literals heap p addresses kind mode reason hk modeLoaded condition)
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
    p logger environment addresses kind mode reason name effect address external hk hm condition hl hg he
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have all := StaticErrors.failure_all_behaviors (ErrorContext.static objects literals) program (Runtime.function model signature)
    (arguments (some p) addresses) heap heap p (messages reason) category logger (message reason) name environment _
    (External.observed (Logging.signature name) effect) (body_agrees model objects literals)
    (failure_prefix model literals heap p addresses kind mode reason hk modeLoaded condition)
    defined helper (messageBound reason) address external rfl categoryBound hm hl hg he
  constructor
  · intro behavior
    exact (all behavior).trans (observed_choices effect _ _ (fun _ after => ⟨.integer 3, after⟩) behavior)
  · intro value after executed
    have successful := (all (.terminates [⟨name, Logging.arguments environment category (messages reason)⟩]
      ⟨.integer 3, after⟩)).mpr (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := CCalls.Events.termination_preserves successful
    exact ⟨categoryStored.preserved preserved, (messageStored reason).preserved preserved⟩

end Rumoca.FMI3.DiscreteCalls
