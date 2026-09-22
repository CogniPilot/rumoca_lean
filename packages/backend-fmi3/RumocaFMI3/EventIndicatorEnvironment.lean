import RumocaFMI3.EventIndicatorContract
import RumocaFMI3.RuntimeEnvironment
import RumocaFMI3.StaticErrorCalls
import RumocaC.BodyCallInterface

noncomputable section
namespace Rumoca.FMI3.EventIndicatorEnvironment
open CTree CMemory CBody StaticFactory CLiteral CLiteral.Interface CCalls
set_option maxRecDepth 10000

theorem body_agrees (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    CodeAgrees (cInterface literals) (RuntimeEnvironment.interface header objects literals)
      (Runtime.body model EventIndicatorCalls.signature) := by
  rw [EventIndicatorCalls.body_eq]
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, EventIndicatorCalls.tail,
    Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression,
    permittedModes, Runtime.mode, Runtime.ok, Runtime.reject, Runtime.fail,
    Runtime.branch, Runtime.ret, Runtime.any, Runtime.both, Runtime.either, Runtime.negate,
    Runtime.eqv, Runtime.nev, Runtime.field, Runtime.call, Runtime.v, Runtime.n,
    Expr.nullPointer, RuntimeEnvironment.interface, CFenv.Header.interface,
    CInterface.constants, objectConstants]

/-- The same body is interpreted in the actual factory/lifecycle interface.
The empty output imposes no pointed-to storage or numerical helper premise. -/
theorem quiet_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : Events.Program E) (heap : Heap),
      program.internal.definitions EventIndicatorCalls.signature.name =
        some (.tree (Runtime.function model EventIndicatorCalls.signature)) →
      EventIndicatorCalls.QuietContract program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap defined
  constructor
  · intro p buffer mode hk hm allowed behavior
    have executed : @CBody.run (cInterface literals) 5
        (.running (Runtime.body model EventIndicatorCalls.signature) (EventIndicatorCalls.parameters (some p) buffer 0) heap) =
        some (.returned ⟨.integer 0, heap⟩) := by
      letI : CInterface := cInterface literals
      rw [show 5 = 4 + 1 from rfl, CBody.run_add,
        EventIndicatorCalls.accepted_run (static := ⟨literals⟩) model heap p buffer mode hk hm allowed]
      simp [CBody.run, CBody.next, CBody.nextWith, CBody.legacyExpressions,
        CBody.eval, CBody.evalWith, Runtime.ok, Runtime.ret, Runtime.v,
        EventIndicatorCalls.locals, EventIndicatorCalls.parameters, CBody.bind, CBody.resolve, CBody.constants]
    exact Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals)
      (RuntimeEnvironment.types_agree header objects literals) rfl
      program (Runtime.function model EventIndicatorCalls.signature) _ _ heap _ (.integer 0) 5 defined
      (EventIndicatorCalls.parameters_bound (static := ⟨literals⟩) (some p) buffer 0)
      (BodyEmbedding.body_closed model EventIndicatorCalls.signature) (body_agrees header objects literals model)
      executed rfl behavior
  · intro buffer count behavior
    let rest := Runtime.modeGuard .getDerivatives :: EventIndicatorCalls.tail
    have executed := GuardedCalls.null_body (static := ⟨literals⟩)
      (EventIndicatorCalls.parameters none buffer count) heap rest
      (by simp [EventIndicatorCalls.parameters, CBody.bind])
      (by simp [EventIndicatorCalls.parameters, CBody.bind])
      (by simp [EventIndicatorCalls.parameters, CBody.bind])
    have body : (Runtime.function model EventIndicatorCalls.signature).body = Runtime.instancePrefix ++ rest := by
      simp [Runtime.function, EventIndicatorCalls.body_eq, Runtime.require, rest, List.append_assoc]
    rw [← body] at executed
    exact Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals)
      (RuntimeEnvironment.types_agree header objects literals) rfl
      program (Runtime.function model EventIndicatorCalls.signature) _ _ heap _ (.integer 3) 3 defined
      (EventIndicatorCalls.parameters_bound (static := ⟨literals⟩) none buffer count)
      (BodyEmbedding.body_closed model EventIndicatorCalls.signature) (body_agrees header objects literals model)
      executed rfl behavior

end Rumoca.FMI3.EventIndicatorEnvironment

namespace Rumoca.FMI3.EventIndicatorEnvironment
open CTree CMemory CBody StaticFactory CLiteral CLiteral.Interface

def SuppressedContract [CInterface] (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ (access : Bool) (p : Address) (buffer : Option Address) (count : UInt64)
    (kind : Kind) (mode : Mode) (logger : Option Address) (logging : Bool),
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (boolean logging) →
    EventIndicatorCalls.FailureCondition access kind mode count →
    (logger = none ∨ logging = false) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling EventIndicatorCalls.signature.name (EventIndicatorCalls.values (some p) buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

theorem suppressed_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (messages : Bool → Address),
      program.internal.definitions EventIndicatorCalls.signature.name =
        some (.tree (Runtime.function model EventIndicatorCalls.signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      (∀ access, literals (EventIndicatorCalls.failureMessage access) = some (messages access)) →
      SuppressedContract program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap messages defined helper bound access p buffer count kind mode logger logging
    hk hm hl hg condition suppressed behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  exact StaticErrors.failure_suppressed_behaviors
    ((ErrorContext.static objects literals).withRounding header) program
    (Runtime.function model EventIndicatorCalls.signature) (EventIndicatorCalls.values (some p) buffer count)
    heap heap p (messages access) (EventIndicatorCalls.failureMessage access) _ logger logging
    (body_agrees header objects literals model)
    (EventIndicatorCalls.failure_prefix (static := ⟨literals⟩) model access heap p buffer count
      kind mode hk modeLoaded condition)
    defined helper (bound access) hm hl hg suppressed behavior

theorem logged_correct (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program CCalls.Events.Invocation) (heap : Heap) (signed : Bool)
      (category : Address) (messages : Bool → Address),
      program.internal.definitions EventIndicatorCalls.signature.name =
        some (.tree (Runtime.function model EventIndicatorCalls.signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "logStatus" = some category →
      (∀ access, literals (EventIndicatorCalls.failureMessage access) = some (messages access)) →
      Stored signed heap category "logStatus" →
      (∀ access, Stored signed heap (messages access) (EventIndicatorCalls.failureMessage access)) →
      ∀ access, EventIndicatorCalls.FailureExecutionContract access program category (messages access) heap signed := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap signed category messages defined helper literal bound categoryStored messageStored
    access p logger environment buffer count kind mode name effect address external hk hm hl hg he condition
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have all := StaticErrors.failure_all_behaviors
    ((ErrorContext.static objects literals).withRounding header) program
    (Runtime.function model EventIndicatorCalls.signature) (EventIndicatorCalls.values (some p) buffer count)
    heap heap p (messages access) category logger (EventIndicatorCalls.failureMessage access) name environment _
    (CCalls.Events.External.observed (Logging.signature name) effect)
    (body_agrees header objects literals model)
    (EventIndicatorCalls.failure_prefix (static := ⟨literals⟩) model access heap p buffer count
      kind mode hk modeLoaded condition)
    defined helper (bound access) address external rfl literal hm hl hg he
  constructor
  · intro behavior
    exact (all behavior).trans (CCalls.Events.observed_choices effect _ _
      (fun _ after => ⟨.integer 3, after⟩) behavior)
  · intro value after executed
    have successful := (all (.terminates
      [⟨name, Logging.arguments environment category (messages access)⟩] ⟨.integer 3, after⟩)).mpr
      (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := CCalls.Events.termination_preserves successful
    exact ⟨categoryStored.preserved preserved, (messageStored access).preserved preserved⟩

end Rumoca.FMI3.EventIndicatorEnvironment

namespace Rumoca.FMI3.EventIndicatorEnvironment
open CTree CMemory StaticFactory CLiteral

/-- The actual pool and function table supply event-indicator calls on every later
literal-preserving heap, in the shared creation/lifecycle interface. -/
structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  quiet : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model sigs →
      ∀ heap, EventIndicatorCalls.QuietContract program heap
  failures : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool)
    (objects : Objects) (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ (category : Address) (messages : Bool → Address),
      pool.addresses firstBlock "logStatus" = some category ∧
      (∀ reason, pool.addresses firstBlock (EventIndicatorCalls.failureMessage reason) = some (messages reason)) ∧
      Stored signed heap category "logStatus" ∧
      (∀ reason, Stored signed heap (messages reason) (EventIndicatorCalls.failureMessage reason)) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : CCalls.Events.Program E),
         program.internal = LiteralPreparation.program model sigs → SuppressedContract program heap) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (program : CCalls.Events.Program CCalls.Events.Invocation),
         program.internal = LiteralPreparation.program model sigs →
         ∀ reason, EventIndicatorCalls.FailureExecutionContract reason program
           category (messages reason) heap signed)

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : EventIndicatorCalls.signature ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro program actual heap
    apply quiet_correct header objects (pool.addresses firstBlock) model program heap
    · rw [actual]
      exact LiteralPreparation.function_bound model sigs unique EventIndicatorCalls.signature member
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
      (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" Logging.category_collected firstBlock
    have each : ∀ reason, ∃ message, pool.addresses firstBlock (EventIndicatorCalls.failureMessage reason) = some message := by
      intro reason
      exact LiteralPreparation.message_bound model sigs made EventIndicatorCalls.signature member
        (EventIndicatorCalls.failureMessage reason) (EventIndicatorCalls.failure_message_collected model reason) firstBlock
    choose messages bound using each
    have categoryStored := (pool.storage_valid before firstBlock signed "logStatus" category categoryBound).preserved frame
    have messageStored := fun reason =>
      (pool.storage_valid before firstBlock signed _ (messages reason) (bound reason)).preserved frame
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    have definitions : ∀ (E : Type) (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program model sigs →
        program.internal.definitions EventIndicatorCalls.signature.name =
          some (.tree (Runtime.function model EventIndicatorCalls.signature)) ∧
        program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
      intro E program actual
      constructor
      · rw [actual]
        exact LiteralPreparation.function_bound model sigs unique EventIndicatorCalls.signature member
      · rw [actual]
        exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])
    refine ⟨category, messages, categoryBound, bound, categoryStored, messageStored, ?_, ?_⟩
    · intro E program actual
      obtain ⟨defined, helper⟩ := definitions E program actual
      exact suppressed_correct header objects (pool.addresses firstBlock) model program heap messages defined helper bound
    · intro program actual
      obtain ⟨defined, helper⟩ := definitions CCalls.Events.Invocation program actual
      exact logged_correct header objects (pool.addresses firstBlock) model program heap signed category messages
        defined helper categoryBound bound categoryStored messageStored

end Rumoca.FMI3.EventIndicatorEnvironment
end
