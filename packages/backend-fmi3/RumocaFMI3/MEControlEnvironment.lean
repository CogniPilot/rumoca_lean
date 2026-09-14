import RumocaFMI3.RuntimeEnvironment
import RumocaFMI3.EventEntryCalls
import RumocaFMI3.CompletedCalls
import RumocaFMI3.DiscreteCalls
import RumocaFMI3.StaticErrorCalls

/-! Complete ME control calls in the explicit header/object/literal runtime.
Reuses the existing execution and failure-prefix proofs. These contracts retain
all existing null, rejection and callback outcomes; they do not yet compose
importer state updates, numerical queries or whole ME lifetimes. -/
noncomputable section
namespace Rumoca.FMI3.MEControlEnvironment
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory CLiteral.Interface

theorem null_call {E : Type} (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (fn : Function) (rest : List Stmt)
      (args : List Value) (env : Locals) (heap : Heap),
      program.internal.definitions fn.signature.name = some (.tree fn) →
      @CCalls.parameters (cInterface literals) fn.signature.parameters args = some env →
      fn.body = Runtime.instancePrefix ++ rest → fn.signature.result = "fmi3Status" →
      fn.body.all CBodyEmbedding.closedBlocks = true →
      CodeAgrees (cInterface literals) (RuntimeEnvironment.interface header objects literals) fn.body →
      env "instance" = some (.pointer none) → env "m" = none → env "fmi3Error" = none →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling fn.signature.name args heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program fn rest args env heap defined parameters body status closed agrees hi hn error behavior
  have executed := GuardedCalls.null_body (static := ⟨literals⟩) env heap rest hi hn error
  rw [← body] at executed
  have agreement := body_run_agreement (cInterface literals) (RuntimeEnvironment.interface header objects literals)
    (RuntimeEnvironment.types_agree header objects literals) rfl 3 (.running fn.body env heap) agrees
  have bound := (parameters_agreement (cInterface literals) (RuntimeEnvironment.interface header objects literals)
    (RuntimeEnvironment.types_agree header objects literals) fn.signature.parameters args).symm.trans parameters
  exact CCalls.Events.body_call_behaviors program fn args env heap _ (.integer 3) 3
    defined bound closed (agreement.symm.trans executed) (by rw [status]; rfl) behavior

namespace EntryControl
open EventEntry

theorem body_agrees (header : CFenv.Header) (model : Solve.FMI3Model source) (entry : EventEntry.Entry)
    (objects : Objects) (literals : CLiteralAddresses) :
    CodeAgrees (cInterface literals) (RuntimeEnvironment.interface header objects literals)
      (Runtime.body model (signature entry)) := by
  rw [body]
  cases entry <;>
    simp [CodeAgrees, StmtAgrees, ExprAgrees, names, tail, Entry.command,
      Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression,
      permittedModes, Runtime.put, Runtime.setMode, Runtime.mode, Runtime.ok, Runtime.reject,
      Runtime.fail, Runtime.branch, Runtime.ret, Runtime.any, Runtime.both, Runtime.either,
      Runtime.negate, Runtime.eqv, Runtime.field, Runtime.call, Runtime.v, Runtime.n,
      Runtime.eventTime, Runtime.raiseField, Runtime.lt, Expr.nullPointer,
      RuntimeEnvironment.interface, CFenv.Header.interface, CInterface.constants,
      objectConstants]

theorem call_behaviors {E : Type} (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (entry : EventEntry.Entry) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p : Address) (clock : Time.Clock),
      program.internal.definitions (signature entry).name = some (.tree (Runtime.function model (signature entry))) →
      load heap (p.member "kind") = some (.integer 0) →
      heap (p.member "mode") = some ⟨.int32, true, some (.integer entry.before.code)⟩ →
      (entry = .event → HistoryProofs.Stored heap p clock) →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (signature entry).name [.pointer (some p)] heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, afterHeap entry heap p clock⟩ := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
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
  have agreement := body_run_agreement (cInterface literals) (RuntimeEnvironment.interface header objects literals)
    (RuntimeEnvironment.types_agree header objects literals) rfl n
    (.running (Runtime.body model (signature entry)) (HistoryBodies.parameters p) heap)
    (body_agrees header model entry objects literals)
  have bound : @CCalls.parameters (RuntimeEnvironment.interface header objects literals) (signature entry).parameters
      [.pointer (some p)] = some (HistoryBodies.parameters p) := by cases entry <;> rfl
  exact CCalls.Events.body_call_behaviors program (Runtime.function model (signature entry)) _ _ heap _ (.integer 0) n
    defined bound (BodyEmbedding.body_closed model (signature entry)) (agreement.symm.trans executed) rfl behavior

theorem null_behaviors {E : Type} (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (entry : EventEntry.Entry) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap),
      program.internal.definitions (signature entry).name = some (.tree (Runtime.function model (signature entry))) →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (signature entry).name [.pointer none] heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap defined
  apply MEControlEnvironment.null_call header objects literals program (Runtime.function model (signature entry))
    (Runtime.modeGuard entry.command :: tail entry)
    [.pointer none] StateProofs.nullParameters heap defined rfl
    (by simp [Runtime.function, body, Runtime.require, List.append_assoc]) rfl
    (BodyEmbedding.body_closed model (signature entry)) (body_agrees header model entry objects literals)
  all_goals simp [StateProofs.nullParameters]

theorem quiet_correct {E : Type} (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (entry : EventEntry.Entry) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E),
      program.internal.definitions (signature entry).name = some (.tree (Runtime.function model (signature entry))) →
      QuietContract entry program := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program defined
  exact ⟨fun heap p clock => call_behaviors header objects literals model entry program heap p clock defined,
    fun heap => null_behaviors header objects literals model entry program heap defined⟩

theorem suppressed_correct {E : Type} (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (entry : EventEntry.Entry) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (message : Address) (heap : Heap),
      program.internal.definitions (signature entry).name = some (.tree (Runtime.function model (signature entry))) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals ErrorCalls.rejectionMessage = some message → SuppressedContract entry program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program message heap defined helper messageBound p kind mode logger logging hk hm hl hg suppressed denied behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  exact StaticErrors.failure_suppressed_behaviors ((ErrorContext.static objects literals).withRounding header) program (Runtime.function model (signature entry))
    [.pointer (some p)] heap heap p message ErrorCalls.rejectionMessage _ logger logging
    (body_agrees header model entry objects literals) (failure_prefix model entry literals heap p kind mode hk modeLoaded denied)
    defined helper messageBound hm hl hg suppressed behavior

theorem logged_correct (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (entry : EventEntry.Entry) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program Invocation) (category message : Address) (heap : Heap) (signed : Bool),
      program.internal.definitions (signature entry).name = some (.tree (Runtime.function model (signature entry))) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "logStatus" = some category → literals ErrorCalls.rejectionMessage = some message →
      Stored signed heap category "logStatus" → Stored signed heap message ErrorCalls.rejectionMessage →
      LoggedContract entry program category message heap signed := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program category message heap signed defined helper categoryBound messageBound categoryStored messageStored
    p logger environment kind mode name effect address external hk hm hl hg he denied
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have all := StaticErrors.failure_all_behaviors ((ErrorContext.static objects literals).withRounding header) program (Runtime.function model (signature entry))
    [.pointer (some p)] heap heap p message category logger ErrorCalls.rejectionMessage name environment _
    (External.observed (Logging.signature name) effect) (body_agrees header model entry objects literals)
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

end EntryControl

namespace CompletedControl
open CompletedCalls

theorem body_agrees (header : CFenv.Header) (model : Solve.FMI3Model source) (objects : Objects) (literals : CLiteralAddresses) :
    CodeAgrees (cInterface literals) (RuntimeEnvironment.interface header objects literals) (Runtime.body model signature) := by
  rw [body]
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, tail,
    Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression,
    permittedModes, Runtime.put, Runtime.mode, Runtime.ok, Runtime.reject,
    Runtime.fail, Runtime.branch, Runtime.ret, Runtime.any, Runtime.both, Runtime.either,
    Runtime.negate, Runtime.eqv, Runtime.field, Runtime.call, Runtime.v, Runtime.n,
    Runtime.completedTime, Runtime.raiseField, Runtime.lt, Runtime.pointerCheck, Runtime.out,
    Expr.nullPointer, RuntimeEnvironment.interface, CFenv.Header.interface, CInterface.constants,
      objectConstants]

theorem call_behaviors {E : Type} (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
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
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap p event terminate flag clock defined hk hm stored he ht hne hnt behavior
  obtain ⟨n, executed⟩ := CBody.run_of_reaches (interface := cInterface literals)
    (HistoryBodies.completed_reaches (static := ⟨literals⟩) model signature rfl heap p event terminate flag clock
      stored hk hm he ht hne hnt)
  have agreement := body_run_agreement (cInterface literals) (RuntimeEnvironment.interface header objects literals)
    (RuntimeEnvironment.types_agree header objects literals) rfl n
    (.running (Runtime.body model signature) (HistoryBodies.completedParameters p event terminate flag) heap)
    (body_agrees header model objects literals)
  have bound := (parameters_agreement (cInterface literals) (RuntimeEnvironment.interface header objects literals)
    (RuntimeEnvironment.types_agree header objects literals) signature.parameters
    (arguments (some p) (some event) (some terminate) flag)).symm.trans
      (parameters_bound literals (some p) (some event) (some terminate) flag)
  exact CCalls.Events.body_call_behaviors program (Runtime.function model signature) _ _ heap _ (.integer 0) n
    defined bound (BodyEmbedding.body_closed model signature) (agreement.symm.trans executed) rfl behavior

theorem null_behaviors {E : Type} (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (event terminate : Option Address) (flag : Bool),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling signature.name (arguments none event terminate flag) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap event terminate flag defined
  apply MEControlEnvironment.null_call header objects literals program (Runtime.function model signature)
    (Runtime.modeGuard .completedStep :: Runtime.pointerCheck ["enterEventMode", "terminateSimulation"] :: tail)
    (arguments none event terminate flag) (parameters none event terminate flag) heap defined
    (parameters_bound literals _ _ _ _)
    (by simp [Runtime.function, body, Runtime.require, List.append_assoc]) rfl
    (BodyEmbedding.body_closed model signature) (body_agrees header model objects literals)
  all_goals simp [parameters]

theorem quiet_correct {E : Type} (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      QuietContract program := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program defined
  exact ⟨fun heap p event terminate flag clock =>
    call_behaviors header objects literals model program heap p event terminate flag clock defined,
    fun heap event terminate flag => null_behaviors header objects literals model program heap event terminate flag defined⟩

theorem suppressed_correct {E : Type} (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (messages : Failure → Address) (heap : Heap),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      (∀ reason, literals (message reason) = some (messages reason)) → SuppressedContract program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program messages heap defined helper messageBound p event terminate flag kind mode reason logger logging
    hk hm condition hl hg suppressed behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  exact StaticErrors.failure_suppressed_behaviors ((ErrorContext.static objects literals).withRounding header) program (Runtime.function model signature)
    (arguments (some p) event terminate flag) heap heap p (messages reason) (message reason) _ logger logging
    (body_agrees header model objects literals)
    (failure_prefix model literals heap p event terminate flag kind mode reason hk modeLoaded condition)
    defined helper (messageBound reason) hm hl hg suppressed behavior

theorem logged_correct (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program Invocation) (category : Address) (messages : Failure → Address)
      (heap : Heap) (signed : Bool),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "logStatus" = some category →
      (∀ reason, literals (message reason) = some (messages reason)) →
      Stored signed heap category "logStatus" →
      (∀ reason, Stored signed heap (messages reason) (message reason)) →
      LoggedContract program category messages heap signed := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program category messages heap signed defined helper categoryBound messageBound categoryStored messageStored
    p logger environment event terminate flag kind mode reason name effect address external hk hm condition hl hg he
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have all := StaticErrors.failure_all_behaviors ((ErrorContext.static objects literals).withRounding header) program (Runtime.function model signature)
    (arguments (some p) event terminate flag) heap heap p (messages reason) category logger (message reason) name environment _
    (External.observed (Logging.signature name) effect) (body_agrees header model objects literals)
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

end CompletedControl

namespace DiscreteControl
open DiscreteCalls

theorem body_agrees (header : CFenv.Header) (model : Solve.FMI3Model source) (objects : Objects) (literals : CLiteralAddresses) :
    CodeAgrees (cInterface literals) (RuntimeEnvironment.interface header objects literals) (Runtime.body model signature) := by
  rw [body]
  simp [CodeAgrees, StmtAgrees, ExprAgrees, CLiteral.Interface.names, tail, DiscreteCalls.names, layouts,
    Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression,
    permittedModes, Runtime.mode, Runtime.ok, Runtime.reject,
    Runtime.fail, Runtime.branch, Runtime.ret, Runtime.any, Runtime.both, Runtime.either,
    Runtime.negate, Runtime.eqv, Runtime.field, Runtime.call, Runtime.v, Runtime.n,
    Runtime.pointerCheck, Runtime.out, Expr.nullPointer, RuntimeEnvironment.interface, CFenv.Header.interface, CInterface.constants,
      objectConstants]

theorem call_behaviors {E : Type} (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p : Address) (addresses : String → Address),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      load heap (p.member "kind") = some (.integer 0) →
      load heap (p.member "mode") = some (.integer 2) →
      (∀ entry ∈ outputs addresses, COutputAssignments.Writable heap entry) →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling signature.name (arguments (some p) (fun name => some (addresses name))) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, COutputAssignments.after heap (outputs addresses)⟩ := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap p addresses defined hk hm writable behavior
  have executed := body_run model literals heap p addresses hk hm writable
  have agreement := body_run_agreement (cInterface literals) (RuntimeEnvironment.interface header objects literals)
    (RuntimeEnvironment.types_agree header objects literals) rfl 11
    (.running (Runtime.body model signature) (parameters (some p) (fun name => some (addresses name))) heap)
    (body_agrees header model objects literals)
  have bound := (parameters_agreement (cInterface literals) (RuntimeEnvironment.interface header objects literals)
    (RuntimeEnvironment.types_agree header objects literals) signature.parameters
    (arguments (some p) (fun name => some (addresses name)))).symm.trans (parameters_bound literals _ _)
  exact CCalls.Events.body_call_behaviors program (Runtime.function model signature) _ _ heap _ (.integer 0) 11
    defined bound (BodyEmbedding.body_closed model signature) (agreement.symm.trans executed) rfl behavior

theorem null_behaviors {E : Type} (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (addresses : String → Option Address),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling signature.name (arguments none addresses) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap addresses defined
  apply MEControlEnvironment.null_call header objects literals program (Runtime.function model signature)
    (Runtime.modeGuard .updateDiscrete :: Runtime.pointerCheck DiscreteCalls.names :: tail)
    (arguments none addresses) (parameters none addresses) heap defined (parameters_bound literals _ _)
    (by simp [Runtime.function, body, Runtime.require, List.append_assoc]) rfl
    (BodyEmbedding.body_closed model signature) (body_agrees header model objects literals)
  all_goals simp [parameters, DiscreteCalls.names, layouts]

theorem quiet_correct {E : Type} (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      QuietContract program := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program defined
  exact ⟨fun heap p addresses => call_behaviors header objects literals model program heap p addresses defined,
    fun heap addresses => null_behaviors header objects literals model program heap addresses defined⟩

theorem suppressed_correct {E : Type} (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (messages : Failure → Address) (heap : Heap),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      (∀ reason, literals (message reason) = some (messages reason)) → SuppressedContract program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program messages heap defined helper messageBound p addresses kind mode reason logger logging
    hk hm condition hl hg suppressed behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  exact StaticErrors.failure_suppressed_behaviors ((ErrorContext.static objects literals).withRounding header) program (Runtime.function model signature)
    (arguments (some p) addresses) heap heap p (messages reason) (message reason) _ logger logging
    (body_agrees header model objects literals)
    (failure_prefix model literals heap p addresses kind mode reason hk modeLoaded condition)
    defined helper (messageBound reason) hm hl hg suppressed behavior

theorem logged_correct (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program Invocation) (category : Address) (messages : Failure → Address)
      (heap : Heap) (signed : Bool),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "logStatus" = some category →
      (∀ reason, literals (message reason) = some (messages reason)) →
      Stored signed heap category "logStatus" →
      (∀ reason, Stored signed heap (messages reason) (message reason)) →
      LoggedContract program category messages heap signed := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program category messages heap signed defined helper categoryBound messageBound categoryStored messageStored
    p logger environment addresses kind mode reason name effect address external hk hm condition hl hg he
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have all := StaticErrors.failure_all_behaviors ((ErrorContext.static objects literals).withRounding header) program (Runtime.function model signature)
    (arguments (some p) addresses) heap heap p (messages reason) category logger (message reason) name environment _
    (External.observed (Logging.signature name) effect) (body_agrees header model objects literals)
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

end DiscreteControl

namespace TimeControl
open TimeCalls

theorem suppressed_correct {E : Type} (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (messages : Failure → Address) (heap : Heap),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      (∀ reason, literals (failureMessage reason) = some (messages reason)) → SuppressedContract program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program messages heap defined helper messageBound p bits kind mode window minimum reason logger logging
    hk hm bounds condition hl hg suppressed behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  exact StaticErrors.failure_suppressed_behaviors ((ErrorContext.static objects literals).withRounding header) program (Runtime.function model signature)
    (arguments (some p) bits) heap heap p (messages reason) (failureMessage reason) _ logger logging
    (RuntimeEnvironment.time_body_agrees header model objects literals)
    (failure_prefix (static := ⟨literals⟩) model heap p bits kind mode window minimum reason hk modeLoaded bounds condition)
    defined helper (messageBound reason) hm hl hg suppressed behavior

theorem logged_correct (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program Invocation) (category : Address) (messages : Failure → Address)
      (heap : Heap) (signed : Bool),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "logStatus" = some category →
      (∀ reason, literals (failureMessage reason) = some (messages reason)) →
      Stored signed heap category "logStatus" →
      (∀ reason, Stored signed heap (messages reason) (failureMessage reason)) →
      LoggedContract program category messages heap signed := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program category messages heap signed defined helper categoryBound messageBound categoryStored messageStored
    p logger environment bits kind mode window minimum reason name effect address external hk hm bounds condition hl hg he
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have all := StaticErrors.failure_all_behaviors ((ErrorContext.static objects literals).withRounding header) program (Runtime.function model signature)
    (arguments (some p) bits) heap heap p (messages reason) category logger (failureMessage reason) name environment _
    (External.observed (Logging.signature name) effect) (RuntimeEnvironment.time_body_agrees header model objects literals)
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

end TimeControl

end Rumoca.FMI3.MEControlEnvironment
end
