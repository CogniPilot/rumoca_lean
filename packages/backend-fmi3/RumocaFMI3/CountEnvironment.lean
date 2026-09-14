import RumocaFMI3.CountEntry
import RumocaFMI3.RuntimeEnvironment
import RumocaFMI3.StaticErrorCalls
import RumocaC.ObservedCalls

/-! Count queries in the same interface as static creation and lifecycle.
The prepared contract applies to arbitrary later heaps preserving the literal
pool. Logger effects may branch or have no returning outcome. -/
noncomputable section
namespace Rumoca.FMI3.CountEnvironment
open CTree CMemory CBody StaticFactory CLiteral CLiteral.Interface CountQueries
set_option maxRecDepth 10000

theorem body_agrees (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (events : Bool) :
    CodeAgrees (cInterface literals) (RuntimeEnvironment.interface header objects literals)
      (Runtime.body model (signature events)) := by
  rw [body_eq]
  cases events <;>
    simp [CodeAgrees, StmtAgrees, ExprAgrees, names, rest, outputName, count,
      Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression,
      permittedModes, Runtime.mode, Runtime.ok, Runtime.reject, Runtime.fail,
      Runtime.pointerCheck, Runtime.out, Runtime.branch, Runtime.ret, Runtime.any,
      Runtime.both, Runtime.either, Runtime.negate, Runtime.eqv,
      Runtime.field, Runtime.call, Runtime.v, Runtime.n, Expr.nullPointer,
      RuntimeEnvironment.interface, CFenv.Header.interface, CInterface.constants, objectConstants]

structure QuietContract [CInterface] (events : Bool)
    (program : CCalls.Events.Program E) (heap : Heap) : Prop where
  successful : ∀ p buffer kind mode old,
    load heap (p.member "kind") = some (.integer kind.code) →
    load heap (p.member "mode") = some (.integer mode.code) →
    Reference.Allowed .getCounts kind mode →
    heap buffer = some ⟨.size, true, old⟩ →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature events).name (arguments (some p) (some buffer)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, written events heap buffer⟩
  null : ∀ buffer behavior, (CCalls.Events.machine program).Behaves
    (.calling (signature events).name (arguments none buffer) heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 3, heap⟩

theorem quiet_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (events : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap),
      program.internal.definitions (signature events).name =
        some (.tree (Runtime.function model (signature events))) →
      QuietContract events program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap defined
  constructor
  · intro p buffer kind mode old hk hm allowed storage behavior
    exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals)
      (RuntimeEnvironment.types_agree header objects literals) rfl
      program (Runtime.function model (signature events)) _ _ heap _ (.integer 0) 6
      defined (parameters_bound (static := ⟨literals⟩) events (some p) (some buffer))
      (BodyEmbedding.body_closed model (signature events)) (body_agrees header objects literals model events)
      (body_run (static := ⟨literals⟩) model events heap p buffer kind mode old hk hm allowed storage)
      (by cases events <;> rfl) behavior
  · intro buffer behavior
    exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals)
      (RuntimeEnvironment.types_agree header objects literals) rfl
      program (Runtime.function model (signature events)) _ _ heap _ (.integer 3) 3
      defined (parameters_bound (static := ⟨literals⟩) events none buffer)
      (BodyEmbedding.body_closed model (signature events)) (body_agrees header objects literals model events)
      (null_run (static := ⟨literals⟩) model events heap buffer)
      (by cases events <;> rfl) behavior

/-- Derive the actual return, output count and memory frame from an arbitrary
returned execution; no expected status or output is a premise. -/
theorem QuietContract.returned [CInterface] (model : Solve.FMI3Model source)
    {events : Bool} {program : CCalls.Events.Program E} {heap : Heap}
    (contract : QuietContract events program heap) (p buffer : Address)
    (kind : Kind) (mode : Mode) (old : Option Value)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getCounts kind mode)
    (storage : heap buffer = some ⟨.size, true, old⟩)
    (observed : List E) (result : CBody.Result)
    (executed : (CCalls.Events.machine program).Behaves
      (.calling (signature events).name (arguments (some p) (some buffer)) heap .done)
      (.terminates observed result)) :
    observed = [] ∧ result.value = .integer 0 ∧
    load result.heap buffer = some (.integer (if events then 0 else model.problem.stateShape.volume)) ∧
    (∀ q, q ≠ buffer → result.heap q = heap q) := by
  have same := (contract.successful p buffer kind mode old hk hm allowed storage _).mp executed
  injection same with observedEq resultEq
  subst observed
  subst result
  refine ⟨rfl, rfl, ?_, CountQueries.frame events heap buffer⟩
  cases events <;> exact stored_count _ heap buffer

/-- Suppression includes either a disabled flag or a missing callback. -/
def SuppressedContract [CInterface] (events : Bool)
    (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ (missing : Bool) (p : Address) (buffer : Option Address) (kind : Kind) (mode : Mode)
    (logger : Option Address) (logging : Bool),
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (boolean logging) →
    FailureCondition missing kind mode buffer →
    (logger = none ∨ logging = false) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature events).name (arguments (some p) buffer) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

theorem suppressed_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (events : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (messages : Bool → Address),
      program.internal.definitions (signature events).name =
        some (.tree (Runtime.function model (signature events))) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      (∀ missing, literals (failureMessage missing) = some (messages missing)) →
      SuppressedContract events program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap messages defined helper bound missing p buffer kind mode logger logging
    hk hm hl hg condition suppressed behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  exact StaticErrors.failure_suppressed_behaviors
    ((ErrorContext.static objects literals).withRounding header) program
    (Runtime.function model (signature events)) (arguments (some p) buffer)
    heap heap p (messages missing) (failureMessage missing) _ logger logging
    (body_agrees header objects literals model events)
    (failure_prefix (static := ⟨literals⟩) model events missing heap p buffer kind mode hk modeLoaded condition)
    defined helper (bound missing) hm hl hg suppressed behavior

def LoggedContract [CInterface] (events missing : Bool)
    (program : CCalls.Events.Program CCalls.Events.Invocation)
    (category message : Address) (heap : Heap) (signed : Bool) : Prop :=
  ∀ (p logger : Address) (environment buffer : Option Address) (kind : Kind) (mode : Mode)
    (name : String) (effect : CCalls.Events.ReturningEffect (Logging.signature name)),
    program.addresses logger = some name →
    program.externals name = some (CCalls.Events.External.observed (Logging.signature name) effect) →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    FailureCondition missing kind mode buffer →
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature events).name (arguments (some p) buffer) heap .done) behavior ↔
      (∃ value after, effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after ∧
        behavior = .terminates [⟨name, Logging.arguments environment category message⟩] ⟨.integer 3, after⟩) ∨
      ((∀ value after, ¬ effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after) ∧ behavior = .wrong [])) ∧
    (∀ value after, effect.execute (Logging.arguments environment category message)
      (LifecycleBodies.writeMode heap p .terminated) value after →
      Stored signed after category "logStatus" ∧ Stored signed after message (failureMessage missing))

theorem logged_correct (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (events : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program CCalls.Events.Invocation) (heap : Heap) (signed : Bool)
      (category : Address) (messages : Bool → Address),
      program.internal.definitions (signature events).name =
        some (.tree (Runtime.function model (signature events))) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "logStatus" = some category →
      (∀ missing, literals (failureMessage missing) = some (messages missing)) →
      Stored signed heap category "logStatus" →
      (∀ missing, Stored signed heap (messages missing) (failureMessage missing)) →
      ∀ missing, LoggedContract events missing program category (messages missing) heap signed := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap signed category messages defined helper literal bound categoryStored messageStored
    missing p logger environment buffer kind mode name effect address external hk hm hl hg he condition
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have all := StaticErrors.failure_all_behaviors
    ((ErrorContext.static objects literals).withRounding header) program
    (Runtime.function model (signature events)) (arguments (some p) buffer)
    heap heap p (messages missing) category logger (failureMessage missing) name environment _
    (CCalls.Events.External.observed (Logging.signature name) effect)
    (body_agrees header objects literals model events)
    (failure_prefix (static := ⟨literals⟩) model events missing heap p buffer kind mode hk modeLoaded condition)
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

/-- The actual pool and function table supply a count query on every later
literal-preserving heap, in the shared creation/lifecycle interface. -/
structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature) (events : Bool)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  quiet : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model sigs →
      ∀ heap, QuietContract events program heap
  failures : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool)
    (objects : Objects) (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ (category : Address) (messages : Bool → Address),
      pool.addresses firstBlock "logStatus" = some category ∧
      (∀ missing, pool.addresses firstBlock (failureMessage missing) = some (messages missing)) ∧
      Stored signed heap category "logStatus" ∧
      (∀ missing, Stored signed heap (messages missing) (failureMessage missing)) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : CCalls.Events.Program E),
         program.internal = LiteralPreparation.program model sigs → SuppressedContract events program heap) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (program : CCalls.Events.Program CCalls.Events.Invocation),
         program.internal = LiteralPreparation.program model sigs →
         ∀ missing, LoggedContract events missing program category (messages missing) heap signed)

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature) (events : Bool)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature events ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs events pool := by
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro program actual heap
    apply quiet_correct header objects (pool.addresses firstBlock) model events program heap
    rw [actual]
    exact LiteralPreparation.function_bound model sigs unique (signature events) member
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
      (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" Logging.category_collected firstBlock
    have each : ∀ missing, ∃ message, pool.addresses firstBlock (failureMessage missing) = some message := by
      intro missing
      exact LiteralPreparation.message_bound model sigs made (signature events) member
        (failureMessage missing) (message_collected model events missing) firstBlock
    choose messages bound using each
    have categoryStored := (pool.storage_valid before firstBlock signed "logStatus" category categoryBound).preserved frame
    have messageStored := fun missing =>
      (pool.storage_valid before firstBlock signed _ (messages missing) (bound missing)).preserved frame
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    have definitions : ∀ (E : Type) (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program model sigs →
        program.internal.definitions (signature events).name =
          some (.tree (Runtime.function model (signature events))) ∧
        program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
      intro E program actual
      constructor
      · rw [actual]
        exact LiteralPreparation.function_bound model sigs unique (signature events) member
      · rw [actual]
        exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])
    refine ⟨category, messages, categoryBound, bound, categoryStored, messageStored, ?_, ?_⟩
    · intro E program actual
      obtain ⟨defined, helper⟩ := definitions E program actual
      exact suppressed_correct header objects (pool.addresses firstBlock) model events program heap messages defined helper bound
    · intro program actual
      obtain ⟨defined, helper⟩ := definitions CCalls.Events.Invocation program actual
      exact logged_correct header objects (pool.addresses firstBlock) model events program heap signed category messages
        defined helper categoryBound bound categoryStored messageStored

end Rumoca.FMI3.CountEnvironment
end
