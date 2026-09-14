import RumocaFMI3.RuntimeEnvironment
import RumocaFMI3.ModelRhsRuntime
import RumocaFMI3.DerivativeContract
import RumocaFMI3.StaticErrorCalls

noncomputable section
namespace Rumoca.FMI3.DerivativeEnvironment
open CTree CMemory CBody StaticFactory CLiteral CLiteral.Interface CCalls
set_option maxRecDepth 10000

theorem body_agrees (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    CodeAgrees (cInterface literals) (RuntimeEnvironment.interface header objects literals)
      (Runtime.body model DerivativeCalls.signature) := by
  rw [DerivativeCalls.body_eq]
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, DerivativeCalls.tail,
    DerivativeCalls.action, DerivativeCalls.target, Runtime.scalarAccessCheck,
    Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression,
    permittedModes, Runtime.mode, Runtime.ok, Runtime.reject, Runtime.fail,
    Runtime.branch, Runtime.ret, Runtime.any, Runtime.both, Runtime.either, Runtime.negate,
    Runtime.eqv, Runtime.nev, Runtime.field, Runtime.call, Runtime.v, Runtime.n,
    Expr.nullPointer, RuntimeEnvironment.interface, CFenv.Header.interface,
    CInterface.constants, objectConstants]

/-- The public getter's actual entry, guard, nested helper/kernel call, caller
output write and status return all use the shared runtime environment. -/
theorem get_reaches {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : Events.Program E) (heap : Heap) (p buffer : Address) (mode : Mode)
      (state : ModelExchange.State) (old : Option Value) (stack : Typed.Continuation),
      program.internal.definitions DerivativeCalls.signature.name =
        some (.tree (Runtime.function model DerivativeCalls.signature)) →
      program.internal.definitions "model_rhs" = some (.tree Runtime.helpers[1]) →
      program.internal.definitions "rumoca_rhs" = some (.kernel .rhs) →
      program.internal.kernel = CExecution.program model.solve →
      load heap (p.member "kind") = some (.integer 0) →
      load heap (p.member "mode") = some (.integer mode.code) →
      Reference.Allowed .getDerivatives .me mode → heap buffer = some ⟨.float64, true, old⟩ →
      Transition.Reaches (fun s t => Events.internalNext program s = some t)
        (.calling DerivativeCalls.signature.name (DerivativeCalls.values (some p) (some buffer) 1) heap stack)
        (.returning (.integer 0) (StateProofs.written heap buffer
          (Binary64.toBits (ModelExchange.derivative model.solve state)).val) stack) := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap p buffer mode state old stack defined helper numerical same hk hm allowed storage
  have bound := (parameters_agreement (cInterface literals)
    (RuntimeEnvironment.interface header objects literals)
    (RuntimeEnvironment.types_agree header objects literals) _ _).symm.trans
    (DerivativeCalls.parameters_bound (static := ⟨literals⟩) (some p) (some buffer) 1)
  have accepted := (body_run_agreement (cInterface literals)
    (RuntimeEnvironment.interface header objects literals)
    (RuntimeEnvironment.types_agree header objects literals) rfl 4
    (.running (Runtime.body model DerivativeCalls.signature)
      (DerivativeCalls.parameters (some p) (some buffer) 1) heap)
    (body_agrees header objects literals model)).symm.trans
    (DerivativeCalls.accepted_run (static := ⟨literals⟩) model heap p buffer mode hk hm allowed)
  obtain ⟨types, entered⟩ := Events.body_prefix_reaches program (Runtime.function model DerivativeCalls.signature)
    (DerivativeCalls.values (some p) (some buffer) 1) (DerivativeCalls.parameters (some p) (some buffer) 1)
    (DerivativeCalls.locals p (some buffer) 1) heap heap DerivativeCalls.action stack 4
    defined bound (BodyEmbedding.body_closed model DerivativeCalls.signature) accepted
  let env := DerivativeCalls.locals p (some buffer) 1
  let saved := DerivativeCalls.continuation env types stack
  have rhsBinding : CInterface.constants "model_rhs" = none := rfl
  have okBinding : CInterface.constants "fmi3OK" = some (.integer 0) := rfl
  have called : Events.internalNext program
      (.body (.running DerivativeCalls.action env types heap) "fmi3Status" stack) =
      some (.calling "model_rhs" [.pointer (some (p.member "model"))] heap saved) := by
    simp [Events.internalNext, Typed.nextWith, CLoops.next, CLoops.eval,
      DerivativeCalls.action, DerivativeCalls.target, Runtime.call, Runtime.field, Runtime.v, Runtime.n,
      CBody.eval, CBody.lvalue, Events.enterCall, Events.resolve, Indirect.operand, Indirect.resolve,
      arguments, env, DerivativeCalls.locals, DerivativeCalls.parameters, CBody.bind, resolve, constants,
      Value.address, saved, DerivativeCalls.continuation, rhsBinding]
  refine entered.trans (.next called ?_)
  have helperTypes : ModelRhsRuntime.Types := ⟨rfl, rfl, rfl⟩
  refine (ModelRhsRuntime.reaches program helperTypes model.solve same helper numerical
    heap (some (p.member "model")) saved).trans ?_
  let after := StateProofs.written heap buffer (Binary64.toBits model.solve.realRhs).val
  refine .next (t := .body (.running [Runtime.ok] env types after) "fmi3Status" stack) ?_ ?_
  · simp [Events.internalNext, Typed.nextWith, Typed.resume, saved, DerivativeCalls.continuation,
      DerivativeCalls.target, Runtime.v, Runtime.n, CBody.lvalue, CBody.eval, env, DerivativeCalls.locals,
      DerivativeCalls.parameters, CBody.bind, resolve, constants, Value.address, Value.finite,
      store_float64 heap buffer old _ storage, after, StateProofs.written]
  refine .next (t := .body (.returned ⟨.integer 0, after⟩) "fmi3Status" stack) ?_ (.next ?_ (.refl _))
  · simp [Events.internalNext, Typed.nextWith, CLoops.next, CLoops.eval, Runtime.ok, Runtime.ret,
      Runtime.v, CBody.eval, env, DerivativeCalls.locals, DerivativeCalls.parameters, CBody.bind, resolve, constants, okBinding]
  · rfl

theorem quiet_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : Events.Program E) (heap : Heap),
      program.internal.definitions DerivativeCalls.signature.name =
        some (.tree (Runtime.function model DerivativeCalls.signature)) →
      program.internal.definitions "model_rhs" = some (.tree Runtime.helpers[1]) →
      program.internal.definitions "rumoca_rhs" = some (.kernel .rhs) →
      program.internal.kernel = CExecution.program model.solve →
      DerivativeCalls.QuietExecutionContract model program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap defined helper numerical same
  constructor
  · intro p buffer mode state old hk hm allowed storage behavior
    exact (Events.internal_prefix program
      (get_reaches header objects literals model program heap p buffer mode state old .done
        defined helper numerical same hk hm allowed storage)
      (Events.return_forced program _ _)).behaviors behavior
  · intro buffer count behavior
    let rest := Runtime.modeGuard .getDerivatives :: DerivativeCalls.tail
    have executed := GuardedCalls.null_body (static := ⟨literals⟩)
      (DerivativeCalls.parameters none buffer count) heap rest
      (by simp [DerivativeCalls.parameters, CBody.bind])
      (by simp [DerivativeCalls.parameters, CBody.bind])
      (by simp [DerivativeCalls.parameters, CBody.bind])
    have body : (Runtime.function model DerivativeCalls.signature).body =
        Runtime.instancePrefix ++ rest := by
      simp [Runtime.function, DerivativeCalls.body_eq, Runtime.require, rest, List.append_assoc]
    rw [← body] at executed
    exact Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals)
      (RuntimeEnvironment.types_agree header objects literals) rfl
      program (Runtime.function model DerivativeCalls.signature) _ _ heap _ (.integer 3) 3 defined
      (DerivativeCalls.parameters_bound (static := ⟨literals⟩) none buffer count)
      (BodyEmbedding.body_closed model DerivativeCalls.signature) (body_agrees header objects literals model)
      executed rfl behavior

end Rumoca.FMI3.DerivativeEnvironment

namespace Rumoca.FMI3.DerivativeEnvironment
open CTree CMemory CBody StaticFactory CLiteral CLiteral.Interface

def SuppressedContract [CInterface] (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ (access : Bool) (p : Address) (buffer : Option Address) (count : UInt64)
    (kind : Kind) (mode : Mode) (logger : Option Address) (logging : Bool),
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (boolean logging) →
    DerivativeCalls.FailureCondition access kind mode buffer count →
    (logger = none ∨ logging = false) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling DerivativeCalls.signature.name (DerivativeCalls.values (some p) buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

theorem suppressed_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (messages : Bool → Address),
      program.internal.definitions DerivativeCalls.signature.name =
        some (.tree (Runtime.function model DerivativeCalls.signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      (∀ access, literals (DerivativeCalls.failureMessage access) = some (messages access)) →
      SuppressedContract program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap messages defined helper bound access p buffer count kind mode logger logging
    hk hm hl hg condition suppressed behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  exact StaticErrors.failure_suppressed_behaviors
    ((ErrorContext.static objects literals).withRounding header) program
    (Runtime.function model DerivativeCalls.signature) (DerivativeCalls.values (some p) buffer count)
    heap heap p (messages access) (DerivativeCalls.failureMessage access) _ logger logging
    (body_agrees header objects literals model)
    (DerivativeCalls.failure_prefix (static := ⟨literals⟩) model access heap p buffer count
      kind mode hk modeLoaded condition)
    defined helper (bound access) hm hl hg suppressed behavior

theorem logged_correct (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program CCalls.Events.Invocation) (heap : Heap) (signed : Bool)
      (category : Address) (messages : Bool → Address),
      program.internal.definitions DerivativeCalls.signature.name =
        some (.tree (Runtime.function model DerivativeCalls.signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "logStatus" = some category →
      (∀ access, literals (DerivativeCalls.failureMessage access) = some (messages access)) →
      Stored signed heap category "logStatus" →
      (∀ access, Stored signed heap (messages access) (DerivativeCalls.failureMessage access)) →
      ∀ access, DerivativeCalls.FailureExecutionContract access program category (messages access) heap signed := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap signed category messages defined helper literal bound categoryStored messageStored
    access p logger environment buffer count kind mode name effect address external hk hm hl hg he condition
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have all := StaticErrors.failure_all_behaviors
    ((ErrorContext.static objects literals).withRounding header) program
    (Runtime.function model DerivativeCalls.signature) (DerivativeCalls.values (some p) buffer count)
    heap heap p (messages access) category logger (DerivativeCalls.failureMessage access) name environment _
    (CCalls.Events.External.observed (Logging.signature name) effect)
    (body_agrees header objects literals model)
    (DerivativeCalls.failure_prefix (static := ⟨literals⟩) model access heap p buffer count
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

end Rumoca.FMI3.DerivativeEnvironment

namespace Rumoca.FMI3.DerivativeEnvironment
open CTree CMemory StaticFactory CLiteral

/-- The actual pool and function table supply derivative calls on every later
literal-preserving heap, in the shared creation/lifecycle interface. -/
structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  quiet : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model sigs →
      ∀ heap, DerivativeCalls.QuietExecutionContract model program heap
  failures : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool)
    (objects : Objects) (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ (category : Address) (messages : Bool → Address),
      pool.addresses firstBlock "logStatus" = some category ∧
      (∀ reason, pool.addresses firstBlock (DerivativeCalls.failureMessage reason) = some (messages reason)) ∧
      Stored signed heap category "logStatus" ∧
      (∀ reason, Stored signed heap (messages reason) (DerivativeCalls.failureMessage reason)) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : CCalls.Events.Program E),
         program.internal = LiteralPreparation.program model sigs → SuppressedContract program heap) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (program : CCalls.Events.Program CCalls.Events.Invocation),
         program.internal = LiteralPreparation.program model sigs →
         ∀ reason, DerivativeCalls.FailureExecutionContract reason program
           category (messages reason) heap signed)

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : DerivativeCalls.signature ∈ sigs)
    (fresh : LiteralPreparation.KernelNamesFresh sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro program actual heap
    apply quiet_correct header objects (pool.addresses firstBlock) model program heap
    · rw [actual]
      exact LiteralPreparation.function_bound model sigs unique DerivativeCalls.signature member
    · rw [actual]
      exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[1] (by simp [Runtime.helpers])
    · rw [actual]
      exact LiteralPreparation.numerical_bound model sigs fresh .rhs
    · rw [actual]
      exact LiteralPreparation.numerical_program model sigs
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
      (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" Logging.category_collected firstBlock
    have each : ∀ reason, ∃ message, pool.addresses firstBlock (DerivativeCalls.failureMessage reason) = some message := by
      intro reason
      exact LiteralPreparation.message_bound model sigs made DerivativeCalls.signature member
        (DerivativeCalls.failureMessage reason) (DerivativeCalls.failure_message_collected model reason) firstBlock
    choose messages bound using each
    have categoryStored := (pool.storage_valid before firstBlock signed "logStatus" category categoryBound).preserved frame
    have messageStored := fun reason =>
      (pool.storage_valid before firstBlock signed _ (messages reason) (bound reason)).preserved frame
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    have definitions : ∀ (E : Type) (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program model sigs →
        program.internal.definitions DerivativeCalls.signature.name =
          some (.tree (Runtime.function model DerivativeCalls.signature)) ∧
        program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
      intro E program actual
      constructor
      · rw [actual]
        exact LiteralPreparation.function_bound model sigs unique DerivativeCalls.signature member
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

end Rumoca.FMI3.DerivativeEnvironment
end
