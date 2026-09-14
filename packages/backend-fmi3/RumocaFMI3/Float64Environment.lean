import RumocaC.CallPrefixInterface
import RumocaFMI3.RuntimeEnvironment
import RumocaFMI3.Float64Contract
import RumocaFMI3.StaticErrorCalls

noncomputable section
namespace Rumoca.FMI3.Float64Environment
open CTree CMemory CBody StaticFactory CLiteral CLiteral.Interface Float64Calls
set_option maxRecDepth 10000

theorem body_agrees (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    CodeAgrees (cInterface literals) (RuntimeEnvironment.interface header objects literals)
      (Runtime.body model (signature false)) := by
  change CodeAgrees _ _ Runtime.getFloat64
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, Runtime.getFloat64,
    Runtime.require, Runtime.countLoop, Runtime.instancePrefix,
    Runtime.modeGuard, Runtime.allowedExpression, permittedModes, Runtime.mode,
    Runtime.ok, Runtime.reject, Runtime.fail, Runtime.branch, Runtime.ret,
    Runtime.any, Runtime.both, Runtime.either, Runtime.negate, Runtime.eqv,
    Runtime.nev, Runtime.lt, Runtime.gt, Runtime.field, Runtime.x, Runtime.call, Runtime.v,
    Runtime.n, Expr.nullPointer, RuntimeEnvironment.interface, CFenv.Header.interface,
    CInterface.constants, objectConstants]

theorem helper_agrees (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) :
    CodeAgrees (cInterface literals) (RuntimeEnvironment.interface header objects literals)
      Runtime.helpers[1].body := by
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, Runtime.helpers, Runtime.ret,
    Runtime.call, Runtime.v, RuntimeEnvironment.interface, CFenv.Header.interface,
    CInterface.constants, objectConstants]

/-- Failure and empty prefixes use only the accessor. Successful derivative
queries additionally use its existing helper and numerical RHS definition. -/
def fragment (literals : CLiteralAddresses) (model : Solve.FMI3Model source)
    (kernel : CSyntax.Program) (addresses : Address → Option String) (needsRhs : Bool) :
    @CCalls.Events.Program (cInterface literals) E :=
  @CCalls.Events.Program.internalOnly E (cInterface literals)
    ⟨fun name => if name = (signature false).name then
        some (.tree (Runtime.function model (signature false)))
      else if needsRhs = true ∧ name = "model_rhs" then some (.tree Runtime.helpers[1])
      else if needsRhs = true ∧ name = "rumoca_rhs" then some (.kernel .rhs)
      else none, kernel⟩ addresses

theorem reaches {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (needsRhs : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (args : List Value) (heap : Heap)
      (final : CCalls.Typed.State),
      program.internal.definitions (signature false).name =
        some (.tree (Runtime.function model (signature false))) →
      (needsRhs = true →
        program.internal.definitions "model_rhs" = some (.tree Runtime.helpers[1]) ∧
        program.internal.definitions "rumoca_rhs" = some (.kernel .rhs)) →
      Transition.Reaches (fun s t => @CCalls.Events.internalNext E (cInterface literals)
        (fragment (E := E) literals model program.internal.kernel program.addresses needsRhs) s = some t)
        (.calling (signature false).name args heap .done) final →
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling (signature false).name args heap .done) final := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program args heap final defined helpers run
  apply CCalls.Events.internal_reaches_interface (cInterface literals)
    (RuntimeEnvironment.interface header objects literals)
    (RuntimeEnvironment.types_agree header objects literals) rfl
    (fragment (E := E) literals model program.internal.kernel program.addresses needsRhs) program
    (s := .calling (signature false).name args heap .done)
    ?_ rfl rfl ?_ StackAgrees.done run
  · intro name fn found
    simp only [fragment, CCalls.Events.Program.internalOnly] at found
    split at found
    · rename_i same
      cases Option.some.inj found
      simpa only [same] using defined
    · split at found
      · rename_i present
        cases Option.some.inj found
        simpa only [present.2] using (helpers present.1).1
      · split at found
        · rename_i present
          cases Option.some.inj found
          simpa only [present.2] using (helpers present.1).2
        · contradiction
  · intro name fn found
    simp only [fragment, CCalls.Events.Program.internalOnly] at found
    split at found
    · cases Option.some.inj found
      exact body_agrees header objects literals model
    · split at found
      · cases Option.some.inj found
        exact helper_agrees header objects literals
      · split at found <;> simp at found

/-- Complete batched getter execution in the creation/lifecycle runtime.
The original finite state/time and caller storage determine every result;
the helper uses the actual prepared numerical program and does not advance it. -/
theorem quiet_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap),
      program.internal.definitions (signature false).name =
        some (.tree (Runtime.function model (signature false))) →
      program.internal.definitions "model_rhs" = some (.tree Runtime.helpers[1]) →
      program.internal.definitions "rumoca_rhs" = some (.kernel .rhs) →
      program.internal.kernel = CExecution.program model.solve →
      Float64Calls.QuietExecutionContract model program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap defined helper numerical same
  constructor
  · intro p input buffer n shape references kind mode state time volume hk hm allowed readable valid
      writable referencesSeparate stateStored stateSeparate timeStored timeSeparate behavior
    have executed := get_reaches (static := ⟨literals⟩) model
      (fragment (E := E) literals model program.internal.kernel program.addresses true)
      heap p input buffer n shape references kind mode state time .done volume
      (by simp [fragment, CCalls.Events.Program.internalOnly]) hk hm allowed readable valid
      writable referencesSeparate stateStored stateSeparate timeStored timeSeparate
      (by simp [fragment, CCalls.Events.Program.internalOnly, signature])
      (by simp [fragment, CCalls.Events.Program.internalOnly, signature]) same
    exact (CCalls.Events.internal_prefix program
      (reaches header objects literals model true program _ heap _ defined (fun _ => ⟨helper, numerical⟩) executed)
      (CCalls.Events.return_forced program _ _)).behaviors behavior
  · intro p input buffer kind mode hk hm allowed behavior
    have executed := empty_get_reaches (static := ⟨literals⟩) model
      (fragment (E := E) literals model program.internal.kernel program.addresses false)
      heap p input buffer kind mode .done
      (by simp [fragment, CCalls.Events.Program.internalOnly]) hk hm allowed
    exact (CCalls.Events.internal_prefix program
      (reaches header objects literals model false program _ heap _ defined (by simp) executed)
      (CCalls.Events.return_forced program _ _)).behaviors behavior
  · intro input buffer n m behavior
    have executed := GuardedCalls.null_body (static := ⟨literals⟩)
      (parameters none input buffer n m) heap (Runtime.modeGuard .get :: getTail)
      (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind])
      (by simp [parameters, CBody.bind])
    exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals)
      (RuntimeEnvironment.types_agree header objects literals) rfl
      program (Runtime.function model (signature false)) _ _ heap _ (.integer 3) 3
      defined (parameters_bound (static := ⟨literals⟩) false _ _ _ _ _)
      (BodyEmbedding.body_closed model (signature false)) (body_agrees header objects literals model)
      executed rfl behavior

/-- Rejections stop before any RHS dispatch, so helper/numerical bindings
and finite model/output storage are not added to the failure premises. -/
theorem failure_site {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
      (input buffer : Option Address) (n m : UInt64) (references : Nat → UInt32)
      (kind : Kind) (mode : Mode) (reason : GetFailure),
      program.internal.definitions (signature false).name =
        some (.tree (Runtime.function model (signature false))) →
      load heap (p.member "kind") = some (.integer kind.code) →
      load heap (p.member "mode") = some (.integer mode.code) →
      Reference.Allowed .get kind mode →
      (reason = .reference → References heap input n.toNat references) →
      FailureCondition reason input buffer n m references →
      GuardedCalls.FailureSite program
        (.calling (signature false).name (arguments (some p) input buffer n m) heap .done)
        heap p (failureMessage reason) := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap p input buffer n m references kind mode reason defined hk hm allowed readable condition
  obtain ⟨env, types, rest, executed, unshadowed, instanceBound⟩ :=
    Float64Calls.failure_site (static := ⟨literals⟩) model
      (fragment (E := E) literals model program.internal.kernel program.addresses false)
      heap p input buffer n m references kind mode reason
      (by simp [fragment, CCalls.Events.Program.internalOnly]) hk hm allowed readable condition
  exact ⟨env, types, rest,
    reaches header objects literals model false program _ heap _ defined (by simp) executed,
    unshadowed, instanceBound⟩

end Rumoca.FMI3.Float64Environment
end

noncomputable section
namespace Rumoca.FMI3.Float64Environment
open CTree CMemory CBody StaticFactory CLiteral Float64Calls

/-- Every existing getter rejection, with disabled or absent logging. -/
def SuppressedContract [CInterface] (reason : Float64Calls.GetFailure)
    (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ p input buffer n m references kind mode logger logging,
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (boolean logging) →
    Reference.Allowed .get kind mode →
    (reason = .reference → References heap input n.toNat references) →
    Float64Calls.FailureCondition reason input buffer n m references →
    (logger = none ∨ logging = false) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature false).name (arguments (some p) input buffer n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

theorem suppressed_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (reason : Float64Calls.GetFailure) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (message : Address),
      program.internal.definitions (signature false).name =
        some (.tree (Runtime.function model (signature false))) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals (Float64Calls.failureMessage reason) = some message →
      SuppressedContract reason program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap message defined helper bound p input buffer n m references kind mode
    logger logging hk hm hl hg allowed readable condition suppressed behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  obtain ⟨env, types, rest, reached, unshadowed, instanceBound⟩ :=
    failure_site header objects literals model program heap p input buffer n m references
      kind mode reason defined hk modeLoaded allowed readable condition
  rw [CCalls.Events.internal_prefix_behaviors program reached behavior]
  exact StaticErrors.statement_suppressed_behaviors
    ((ErrorContext.static objects literals).withRounding header) program env types rest
    (Float64Calls.failureMessage reason) heap p message _ logger logging
    unshadowed instanceBound helper bound hm hl hg suppressed behavior

theorem logged_correct (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (reason : Float64Calls.GetFailure) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program CCalls.Events.Invocation) (heap : Heap)
      (signed : Bool) (category message : Address),
      program.internal.definitions (signature false).name =
        some (.tree (Runtime.function model (signature false))) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "logStatus" = some category →
      literals (Float64Calls.failureMessage reason) = some message →
      Stored signed heap category "logStatus" →
      Stored signed heap message (Float64Calls.failureMessage reason) →
      Float64Calls.FailureExecutionContract reason program category message heap signed := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap signed category message defined helper literal bound categoryStored messageStored
    p logger environment input buffer n m references kind mode name effect address external
    hk hm hl hg he allowed readable condition
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  obtain ⟨env, types, rest, reached, unshadowed, instanceBound⟩ :=
    failure_site header objects literals model program heap p input buffer n m references
      kind mode reason defined hk modeLoaded allowed readable condition
  have tail := StaticErrors.statement_all_behaviors
    ((ErrorContext.static objects literals).withRounding header) program env types rest
    (Float64Calls.failureMessage reason) heap p message category logger environment _ name
    (CCalls.Events.External.observed (Logging.signature name) effect)
    unshadowed instanceBound helper bound address external rfl literal hm hl hg he
  have all := fun behavior =>
    (CCalls.Events.internal_prefix_behaviors program reached behavior).trans (tail behavior)
  constructor
  · intro behavior
    exact (all behavior).trans (CCalls.Events.observed_choices effect _ _
      (fun _ after => ⟨.integer 3, after⟩) behavior)
  · intro value after executed
    have successful := (all (.terminates [⟨name, Logging.arguments environment category message⟩]
      ⟨.integer 3, after⟩)).mpr (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := CCalls.Events.termination_preserves successful
    exact ⟨categoryStored.preserved preserved, messageStored.preserved preserved⟩

/-- The actual getter table and diagnostic pool supply complete batched calls
on later heaps. Read-only diagnostics persist across prior host/runtime actions;
input/output buffers, finite state/time and callback bindings remain explicit. -/
structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  quiet : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model sigs →
      ∀ heap, Float64Calls.QuietExecutionContract model program heap
  failures : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool)
    (objects : Objects) (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ (category : Address) (messages : Float64Calls.GetFailure → Address),
      pool.addresses firstBlock "logStatus" = some category ∧
      (∀ reason, pool.addresses firstBlock (Float64Calls.failureMessage reason) = some (messages reason)) ∧
      Stored signed heap category "logStatus" ∧
      (∀ reason, Stored signed heap (messages reason) (Float64Calls.failureMessage reason)) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : CCalls.Events.Program E),
         program.internal = LiteralPreparation.program model sigs →
         ∀ reason, SuppressedContract reason program heap) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (program : CCalls.Events.Program CCalls.Events.Invocation),
         program.internal = LiteralPreparation.program model sigs →
         ∀ reason, Float64Calls.FailureExecutionContract reason program category (messages reason) heap signed)

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature false ∈ sigs) (fresh : LiteralPreparation.KernelNamesFresh sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro program actual heap
    apply quiet_correct header objects (pool.addresses firstBlock) model program heap
    · rw [actual]
      exact LiteralPreparation.function_bound model sigs unique (signature false) member
    · rw [actual]
      exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[1] (by simp [Runtime.helpers])
    · rw [actual]
      exact LiteralPreparation.numerical_bound model sigs fresh .rhs
    · rw [actual]
      exact LiteralPreparation.numerical_program model sigs
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
      (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" Logging.category_collected firstBlock
    have each : ∀ reason, ∃ message, pool.addresses firstBlock (Float64Calls.failureMessage reason) = some message := by
      intro reason
      exact LiteralPreparation.message_bound model sigs made (signature false) member
        (Float64Calls.failureMessage reason) (Float64Calls.failure_message_collected model reason) firstBlock
    choose messages bound using each
    have categoryStored := (pool.storage_valid before firstBlock signed "logStatus" category categoryBound).preserved frame
    have messageStored := fun reason =>
      (pool.storage_valid before firstBlock signed _ (messages reason) (bound reason)).preserved frame
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    have definitions : ∀ (E : Type) (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program model sigs →
        program.internal.definitions (signature false).name =
          some (.tree (Runtime.function model (signature false))) ∧
        program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
      intro E program actual
      constructor
      · rw [actual]
        exact LiteralPreparation.function_bound model sigs unique (signature false) member
      · rw [actual]
        exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])
    refine ⟨category, messages, categoryBound, bound, categoryStored, messageStored, ?_, ?_⟩
    · intro E program actual reason
      obtain ⟨defined, helper⟩ := definitions E program actual
      exact suppressed_correct header objects (pool.addresses firstBlock) model reason program heap
        (messages reason) defined helper (bound reason)
    · intro program actual reason
      obtain ⟨defined, helper⟩ := definitions CCalls.Events.Invocation program actual
      exact logged_correct header objects (pool.addresses firstBlock) model reason program heap signed
        category (messages reason) defined helper categoryBound (bound reason) categoryStored (messageStored reason)

end Rumoca.FMI3.Float64Environment
end
