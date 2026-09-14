import RumocaFMI3.NominalEntry
import RumocaFMI3.RuntimeEnvironment
import RumocaFMI3.StaticErrorCalls
import RumocaC.ObservedCalls

noncomputable section
namespace Rumoca.FMI3.NominalEnvironment
open CTree CMemory CBody StaticFactory CLiteral CLiteral.Interface Nominals
set_option maxRecDepth 10000

theorem body_agrees (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    CodeAgrees (cInterface literals) (RuntimeEnvironment.interface header objects literals)
      (Runtime.body model ErrorCalls.nominalSignature) := by
  rw [Nominals.body_eq]
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, ErrorCalls.nominalRest,
    Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression,
    permittedModes, Runtime.mode, Runtime.ok, Runtime.reject, Runtime.fail,
    Runtime.scalarAccessCheck, Runtime.branch, Runtime.ret, Runtime.any,
    Runtime.both, Runtime.either, Runtime.negate, Runtime.eqv, Runtime.nev,
    Runtime.field, Runtime.call, Runtime.v, Runtime.n, Expr.nullPointer,
    RuntimeEnvironment.interface, CFenv.Header.interface, CInterface.constants, objectConstants]

theorem quiet_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap),
      program.internal.definitions ErrorCalls.nominalSignature.name =
        some (.tree (Runtime.function model ErrorCalls.nominalSignature)) →
      QuietExecutionContract program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap defined
  constructor
  · intro p buffer kind mode old hk hm allowed storage behavior
    exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals)
      (RuntimeEnvironment.types_agree header objects literals) rfl
      program (Runtime.function model ErrorCalls.nominalSignature) _ _ heap _ (.integer 0) 6
      defined (ErrorCalls.nominal_parameters (static := ⟨literals⟩) p (some buffer) 1)
      (BodyEmbedding.body_closed model ErrorCalls.nominalSignature) (body_agrees header objects literals model)
      (Nominals.body_run (static := ⟨literals⟩) model heap p buffer kind mode old hk hm allowed storage)
      rfl behavior
  · intro buffer count behavior
    exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals)
      (RuntimeEnvironment.types_agree header objects literals) rfl
      program (Runtime.function model ErrorCalls.nominalSignature) _ _ heap _ (.integer 3) 3
      defined (Nominals.null_parameters (static := ⟨literals⟩) buffer count)
      (BodyEmbedding.body_closed model ErrorCalls.nominalSignature) (body_agrees header objects literals model)
      (Nominals.null_body (static := ⟨literals⟩) model heap buffer count) rfl behavior

/-- An arbitrary returned call yields the exact positive nominal and output
frame. The expected value and status are conclusions, not execution premises. -/
theorem quiet_returned [CInterface] {program : CCalls.Events.Program E} {heap : Heap}
    (contract : QuietExecutionContract program heap) (p buffer : Address)
    (kind : Kind) (mode : Mode) (old : Option Value)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getNominals kind mode)
    (storage : heap buffer = some ⟨.float64, true, old⟩)
    (observed : List E) (result : CBody.Result)
    (executed : (CCalls.Events.machine program).Behaves
      (.calling ErrorCalls.nominalSignature.name (ErrorCalls.nominalArguments p (some buffer) 1) heap .done)
      (.terminates observed result)) :
    observed = [] ∧ result.value = .integer 0 ∧
    load result.heap buffer = some (.finite Binary64.one) ∧
    Binary64.value Binary64.one = 1 ∧ 0 < Binary64.value Binary64.one ∧
    (∀ q, q ≠ buffer → result.heap q = heap q) := by
  have same := (contract.successful p buffer kind mode old hk hm allowed storage _).mp executed
  injection same with observedEq resultEq
  subst observed
  subst result
  exact ⟨rfl, rfl, Nominals.stored heap buffer, Binary64.value_one,
    by rw [Binary64.value_one]; exact zero_lt_one, Nominals.frame heap buffer⟩

/-- Suppression includes either a disabled flag or a missing callback. -/
def SuppressedContract [CInterface]
    (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ (missing : Bool) (p : Address) (buffer : Option Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (logger : Option Address) (logging : Bool),
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (boolean logging) →
    FailureCondition missing kind mode buffer count →
    (logger = none ∨ logging = false) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling ErrorCalls.nominalSignature.name (ErrorCalls.nominalArguments p buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

theorem suppressed_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source)  :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (messages : Bool → Address),
      program.internal.definitions ErrorCalls.nominalSignature.name =
        some (.tree (Runtime.function model ErrorCalls.nominalSignature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      (∀ missing, literals (failureMessage missing) = some (messages missing)) →
      SuppressedContract program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap messages defined helper bound missing p buffer count kind mode logger logging
    hk hm hl hg condition suppressed behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  exact StaticErrors.failure_suppressed_behaviors
    ((ErrorContext.static objects literals).withRounding header) program
    (Runtime.function model ErrorCalls.nominalSignature) (ErrorCalls.nominalArguments p buffer count)
    heap heap p (messages missing) (failureMessage missing) _ logger logging
    (body_agrees header objects literals model)
    (failure_prefix (static := ⟨literals⟩) model missing heap p buffer count kind mode hk modeLoaded condition)
    defined helper (bound missing) hm hl hg suppressed behavior

theorem logged_correct (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source)  :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program CCalls.Events.Invocation) (heap : Heap) (signed : Bool)
      (category : Address) (messages : Bool → Address),
      program.internal.definitions ErrorCalls.nominalSignature.name =
        some (.tree (Runtime.function model ErrorCalls.nominalSignature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "logStatus" = some category →
      (∀ missing, literals (failureMessage missing) = some (messages missing)) →
      Stored signed heap category "logStatus" →
      (∀ missing, Stored signed heap (messages missing) (failureMessage missing)) →
      ∀ missing, FailureExecutionContract missing program category (messages missing) heap signed := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap signed category messages defined helper literal bound categoryStored messageStored
    missing p logger environment buffer count kind mode name effect address external hk hm hl hg he condition
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have all := StaticErrors.failure_all_behaviors
    ((ErrorContext.static objects literals).withRounding header) program
    (Runtime.function model ErrorCalls.nominalSignature) (ErrorCalls.nominalArguments p buffer count)
    heap heap p (messages missing) category logger (failureMessage missing) name environment _
    (CCalls.Events.External.observed (Logging.signature name) effect)
    (body_agrees header objects literals model)
    (failure_prefix (static := ⟨literals⟩) model missing heap p buffer count kind mode hk modeLoaded condition)
    defined helper (bound missing) address external rfl literal hm hl hg he
  constructor
  · intro behavior
    exact (all behavior).trans (CCalls.Events.observed_choices effect _ _
      (fun _ after => ⟨.integer 3, after⟩) behavior)
  · intro value after executed
    have successful := (all (.terminates
      [⟨name, Logging.arguments environment category (messages missing)⟩] ⟨.integer 3, after⟩)).mpr
      (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := CCalls.Events.termination_preserves successful
    exact ⟨categoryStored.preserved preserved, (messageStored missing).preserved preserved⟩

/-- The actual pool and function table supply a nominal query on every later
literal-preserving heap, in the shared creation/lifecycle interface. -/
structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  quiet : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model sigs →
      ∀ heap, QuietExecutionContract program heap
  failures : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool)
    (objects : Objects) (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ (category : Address) (messages : Bool → Address),
      pool.addresses firstBlock "logStatus" = some category ∧
      (∀ missing, pool.addresses firstBlock (failureMessage missing) = some (messages missing)) ∧
      Stored signed heap category "logStatus" ∧
      (∀ missing, Stored signed heap (messages missing) (failureMessage missing)) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : CCalls.Events.Program E),
         program.internal = LiteralPreparation.program model sigs → SuppressedContract program heap) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (program : CCalls.Events.Program CCalls.Events.Invocation),
         program.internal = LiteralPreparation.program model sigs →
         ∀ missing, FailureExecutionContract missing program category (messages missing) heap signed)

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : ErrorCalls.nominalSignature ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro program actual heap
    apply quiet_correct header objects (pool.addresses firstBlock) model program heap
    rw [actual]
    exact LiteralPreparation.function_bound model sigs unique ErrorCalls.nominalSignature member
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
      (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" Logging.category_collected firstBlock
    have each : ∀ missing, ∃ message, pool.addresses firstBlock (failureMessage missing) = some message := by
      intro missing
      exact LiteralPreparation.message_bound model sigs made ErrorCalls.nominalSignature member
        (failureMessage missing) (failure_message_collected model missing) firstBlock
    choose messages bound using each
    have categoryStored := (pool.storage_valid before firstBlock signed "logStatus" category categoryBound).preserved frame
    have messageStored := fun missing =>
      (pool.storage_valid before firstBlock signed _ (messages missing) (bound missing)).preserved frame
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    have definitions : ∀ (E : Type) (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program model sigs →
        program.internal.definitions ErrorCalls.nominalSignature.name =
          some (.tree (Runtime.function model ErrorCalls.nominalSignature)) ∧
        program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
      intro E program actual
      constructor
      · rw [actual]
        exact LiteralPreparation.function_bound model sigs unique ErrorCalls.nominalSignature member
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

end Rumoca.FMI3.NominalEnvironment
end
