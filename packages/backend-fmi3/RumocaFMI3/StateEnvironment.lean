import RumocaFMI3.RuntimeEnvironment
import RumocaFMI3.StateContract
import RumocaFMI3.StaticErrorCalls

noncomputable section
namespace Rumoca.FMI3.StateEnvironment
open CTree CMemory CBody StaticFactory CLiteral CLiteral.Interface
set_option maxRecDepth 10000

theorem body_agrees (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (write : Bool) :
    CodeAgrees (cInterface literals) (RuntimeEnvironment.interface header objects literals)
      (Runtime.body model (StateCalls.signature write)) := by
  rw [StateCalls.Entry.body_eq]
  cases write <;>
    simp [CodeAgrees, StmtAgrees, ExprAgrees, names, StateCalls.Entry.command,
      StateCalls.Entry.tail, StateCalls.Entry.action, Runtime.scalarAccessCheck,
      Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression,
      permittedModes, Runtime.mode, Runtime.ok, Runtime.reject, Runtime.fail,
      Runtime.branch, Runtime.ret, Runtime.any, Runtime.both, Runtime.either, Runtime.negate,
      Runtime.eqv, Runtime.nev, Runtime.field, Runtime.x, Runtime.finite, Runtime.call, Runtime.v, Runtime.n,
      Expr.nullPointer, RuntimeEnvironment.interface, CFenv.Header.interface,
      CInterface.constants, objectConstants]

/-- Both actual accessors execute in the creation/lifecycle environment.
The heap is arbitrary; neither a freshly installed pool nor an IVP solution
is a premise for a host trial-state update. -/
theorem quiet_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap),
      (∀ write, program.internal.definitions (StateCalls.signature write).name =
        some (.tree (Runtime.function model (StateCalls.signature write)))) →
      StateCalls.QuietExecutionContract program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap defined
  constructor
  · intro p buffer mode state old hk hm allowed represented storage behavior
    have executed := StateProofs.get_run (static := ⟨literals⟩) model (StateCalls.signature false)
      rfl heap p buffer mode state.x old hk hm allowed represented storage
    exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals)
      (RuntimeEnvironment.types_agree header objects literals) rfl
      program (Runtime.function model (StateCalls.signature false)) _ _ heap _ (.integer 0) 6
      (defined false) (StateCalls.parameters_bound (static := ⟨literals⟩) false p buffer)
      (BodyEmbedding.body_closed model (StateCalls.signature false)) (body_agrees header objects literals model false)
      executed rfl behavior
  · intro p buffer state x hk hm input storage behavior
    have executed := StateProofs.set_run (static := ⟨literals⟩) model (StateCalls.signature true)
      rfl heap p buffer x _ hk hm input storage
    exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals)
      (RuntimeEnvironment.types_agree header objects literals) rfl
      program (Runtime.function model (StateCalls.signature true)) _ _ heap _ (.integer 0) 7
      (defined true) (StateCalls.parameters_bound (static := ⟨literals⟩) true p buffer)
      (BodyEmbedding.body_closed model (StateCalls.signature true)) (body_agrees header objects literals model true)
      executed rfl behavior
  · intro write buffer count behavior
    let rest := Runtime.modeGuard (StateCalls.Entry.command write) :: StateCalls.Entry.tail write
    have executed := GuardedCalls.null_body (static := ⟨literals⟩)
      (StateCalls.Entry.parameters none buffer count) heap rest
      (by simp [StateCalls.Entry.parameters, CBody.bind])
      (by simp [StateCalls.Entry.parameters, CBody.bind])
      (by simp [StateCalls.Entry.parameters, CBody.bind])
    have body : (Runtime.function model (StateCalls.signature write)).body =
        Runtime.instancePrefix ++ rest := by
      simp [Runtime.function, StateCalls.Entry.body_eq, Runtime.require, rest, List.append_assoc]
    rw [← body] at executed
    exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals)
      (RuntimeEnvironment.types_agree header objects literals) rfl
      program (Runtime.function model (StateCalls.signature write)) _ _ heap _ (.integer 3) 3
      (defined write) (StateCalls.Entry.parameters_bound (static := ⟨literals⟩) write none buffer count)
      (BodyEmbedding.body_closed model (StateCalls.signature write)) (body_agrees header objects literals model write)
      executed (by cases write <;> rfl) behavior

/-- Suppression includes either a disabled flag or a missing callback. -/
def SuppressedContract [CInterface] (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ (write : Bool) (reason : StateCalls.Entry.FailureReason) (p : Address)
    (buffer : Option Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (logger : Option Address) (logging : Bool),
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (boolean logging) →
    StateCalls.Entry.FailureCondition reason write kind mode heap buffer count →
    (logger = none ∨ logging = false) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (StateCalls.signature write).name (StateCalls.Entry.values (some p) buffer count)
        heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

theorem suppressed_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap)
      (messages : StateCalls.Entry.FailureReason → Address),
      (∀ write, program.internal.definitions (StateCalls.signature write).name =
        some (.tree (Runtime.function model (StateCalls.signature write)))) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      (∀ reason, literals (StateCalls.Entry.failureMessage reason) = some (messages reason)) →
      SuppressedContract program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap messages defined helper bound write reason p buffer count kind mode logger logging
    hk hm hl hg condition suppressed behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  exact StaticErrors.failure_suppressed_behaviors
    ((ErrorContext.static objects literals).withRounding header) program
    (Runtime.function model (StateCalls.signature write)) (StateCalls.Entry.values (some p) buffer count)
    heap heap p (messages reason) (StateCalls.Entry.failureMessage reason) _ logger logging
    (body_agrees header objects literals model write)
    (StateCalls.Entry.failure_prefix (static := ⟨literals⟩) model write reason heap p buffer count
      kind mode hk modeLoaded condition)
    (defined write) helper (bound reason) hm hl hg suppressed behavior

theorem logged_correct (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program CCalls.Events.Invocation) (heap : Heap) (signed : Bool)
      (category : Address) (messages : StateCalls.Entry.FailureReason → Address),
      (∀ write, program.internal.definitions (StateCalls.signature write).name =
        some (.tree (Runtime.function model (StateCalls.signature write)))) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "logStatus" = some category →
      (∀ reason, literals (StateCalls.Entry.failureMessage reason) = some (messages reason)) →
      Stored signed heap category "logStatus" →
      (∀ reason, Stored signed heap (messages reason) (StateCalls.Entry.failureMessage reason)) →
      ∀ write reason, StateCalls.FailureExecutionContract write reason program category (messages reason) heap signed := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap signed category messages defined helper literal bound categoryStored messageStored
    write reason p logger environment buffer count kind mode name effect address external hk hm hl hg he condition
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have all := StaticErrors.failure_all_behaviors
    ((ErrorContext.static objects literals).withRounding header) program
    (Runtime.function model (StateCalls.signature write)) (StateCalls.Entry.values (some p) buffer count)
    heap heap p (messages reason) category logger (StateCalls.Entry.failureMessage reason) name environment _
    (CCalls.Events.External.observed (Logging.signature name) effect)
    (body_agrees header objects literals model write)
    (StateCalls.Entry.failure_prefix (static := ⟨literals⟩) model write reason heap p buffer count
      kind mode hk modeLoaded condition)
    (defined write) helper (bound reason) address external rfl literal hm hl hg he
  constructor
  · intro behavior
    exact (all behavior).trans (CCalls.Events.observed_choices effect _ _
      (fun _ after => ⟨.integer 3, after⟩) behavior)
  · intro value after executed
    have successful := (all (.terminates
      [⟨name, Logging.arguments environment category (messages reason)⟩] ⟨.integer 3, after⟩)).mpr
      (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := CCalls.Events.termination_preserves successful
    exact ⟨categoryStored.preserved preserved, (messageStored reason).preserved preserved⟩

end Rumoca.FMI3.StateEnvironment

namespace Rumoca.FMI3.StateEnvironment
open CTree CMemory StaticFactory CLiteral

/-- The actual pool and function table supply state calls on every later
literal-preserving heap, in the shared creation/lifecycle interface. -/
structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  quiet : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model sigs →
      ∀ heap, StateCalls.QuietExecutionContract program heap
  failures : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool)
    (objects : Objects) (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ (category : Address) (messages : StateCalls.Entry.FailureReason → Address),
      pool.addresses firstBlock "logStatus" = some category ∧
      (∀ reason, pool.addresses firstBlock (StateCalls.Entry.failureMessage reason) = some (messages reason)) ∧
      Stored signed heap category "logStatus" ∧
      (∀ reason, Stored signed heap (messages reason) (StateCalls.Entry.failureMessage reason)) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : CCalls.Events.Program E),
         program.internal = LiteralPreparation.program model sigs → SuppressedContract program heap) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (program : CCalls.Events.Program CCalls.Events.Invocation),
         program.internal = LiteralPreparation.program model sigs →
         ∀ write reason, StateCalls.FailureExecutionContract write reason program
           category (messages reason) heap signed)

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : ∀ write, StateCalls.signature write ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro program actual heap
    apply quiet_correct header objects (pool.addresses firstBlock) model program heap
    intro write
    rw [actual]
    exact LiteralPreparation.function_bound model sigs unique (StateCalls.signature write) (member write)
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
      (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" Logging.category_collected firstBlock
    have each : ∀ reason, ∃ message, pool.addresses firstBlock (StateCalls.Entry.failureMessage reason) = some message := by
      intro reason
      exact LiteralPreparation.message_bound model sigs made (StateCalls.signature true) (member true)
        (StateCalls.Entry.failureMessage reason) (StateCalls.failure_message_collected model reason) firstBlock
    choose messages bound using each
    have categoryStored := (pool.storage_valid before firstBlock signed "logStatus" category categoryBound).preserved frame
    have messageStored := fun reason =>
      (pool.storage_valid before firstBlock signed _ (messages reason) (bound reason)).preserved frame
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    have definitions : ∀ (E : Type) (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program model sigs →
        (∀ write, program.internal.definitions (StateCalls.signature write).name =
          some (.tree (Runtime.function model (StateCalls.signature write)))) ∧
        program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
      intro E program actual
      constructor
      · intro write
        rw [actual]
        exact LiteralPreparation.function_bound model sigs unique (StateCalls.signature write) (member write)
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

end Rumoca.FMI3.StateEnvironment
end
