import RumocaC.CallPrefixInterface
import RumocaFMI3.RuntimeEnvironment
import RumocaFMI3.Float64SetContract
import RumocaFMI3.StaticErrorCalls

noncomputable section
namespace Rumoca.FMI3.Float64SetEnvironment
open CTree CMemory CBody StaticFactory CLiteral CLiteral.Interface Float64Calls
set_option maxRecDepth 10000

theorem body_agrees (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    CodeAgrees (cInterface literals) (RuntimeEnvironment.interface header objects literals)
      (Runtime.body model (signature true)) := by
  rw [Float64Set.body_eq]
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, Runtime.setFloat64,
    Runtime.setFloat64Values, Runtime.countLoop, Runtime.instancePrefix,
    Runtime.modeGuard, Runtime.allowedExpression, permittedModes, Runtime.mode,
    Runtime.ok, Runtime.reject, Runtime.fail, Runtime.branch, Runtime.ret,
    Runtime.any, Runtime.both, Runtime.either, Runtime.negate, Runtime.eqv,
    Runtime.nev, Runtime.lt, Runtime.field, Runtime.x, Runtime.finite, Runtime.call, Runtime.v,
    Runtime.n, Expr.nullPointer, RuntimeEnvironment.interface, CFenv.Header.interface,
    CInterface.constants, objectConstants]

def fragment (literals : CLiteralAddresses) (model : Solve.FMI3Model source)
    (kernel : CSyntax.Program) (addresses : Address → Option String) :
    @CCalls.Events.Program (cInterface literals) E :=
  @CCalls.Events.Program.internalOnly E (cInterface literals)
    ⟨fun name => if name = (signature true).name then
        some (.tree (Runtime.function model (signature true))) else none, kernel⟩ addresses

/-- A setter prefix can use the same numerical kernel and address table as the
actual runtime without assuming agreement for unrelated public functions. -/
theorem reaches {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (args : List Value) (heap : Heap)
      (final : CCalls.Typed.State),
      program.internal.definitions (signature true).name =
        some (.tree (Runtime.function model (signature true))) →
      Transition.Reaches (fun s t => @CCalls.Events.internalNext E (cInterface literals)
        (fragment (E := E) literals model program.internal.kernel program.addresses) s = some t)
        (.calling (signature true).name args heap .done) final →
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling (signature true).name args heap .done) final := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program args heap final defined run
  apply CCalls.Events.internal_reaches_interface (cInterface literals)
    (RuntimeEnvironment.interface header objects literals)
    (RuntimeEnvironment.types_agree header objects literals) rfl
    (fragment (E := E) literals model program.internal.kernel program.addresses) program
    (s := .calling (signature true).name args heap .done)
    ?_ rfl rfl ?_ StackAgrees.done run
  · intro name fn found
    simp only [fragment, CCalls.Events.Program.internalOnly] at found
    split at found
    · rename_i same
      cases Option.some.inj found
      simpa only [same] using defined
    · contradiction
  · intro name fn found
    simp only [fragment, CCalls.Events.Program.internalOnly] at found
    split at found
    · cases Option.some.inj found
      exact body_agrees header objects literals model
    · contradiction

theorem quiet_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap),
      program.internal.definitions (signature true).name =
        some (.tree (Runtime.function model (signature true))) →
      Float64Set.QuietExecutionContract program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap defined
  constructor
  · intro p input buffer n shape values references kind mode old volume nonempty hk hm
      allowed readable valid loaded stored separate behavior
    have executed := Float64Set.set_reaches (static := ⟨literals⟩) model
      (fragment (E := E) literals model program.internal.kernel program.addresses)
      heap p input buffer n values references kind mode old .done volume nonempty
      (by simp [fragment, CCalls.Events.Program.internalOnly]) hk hm allowed
      readable valid loaded stored separate
    exact (CCalls.Events.internal_prefix program
      (reaches header objects literals model program _ heap _ defined executed)
      (CCalls.Events.return_forced program _ _)).behaviors behavior
  · intro p input buffer kind mode hk hm permitted behavior
    have executed := SetterScope.hoisted_empty_run (static := ⟨literals⟩)
      (parameters (some p) input buffer 0 0) heap p kind mode Runtime.setFloat64Values
      (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind])
      (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind])
      (by simp [parameters, CBody.bind]) hk hm permitted
    exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals)
      (RuntimeEnvironment.types_agree header objects literals) rfl
      program (Runtime.function model (signature true)) _ _ heap _ (.integer 0) 5
      defined (parameters_bound (static := ⟨literals⟩) true _ _ _ _ _)
      (BodyEmbedding.body_closed model (signature true)) (body_agrees header objects literals model)
      executed rfl behavior
  · intro input buffer n m behavior
    have executed := GuardedCalls.null_body (static := ⟨literals⟩)
      (parameters none input buffer n m) heap
      ([Runtime.branch SetterScope.empty [Runtime.modeGuard .setVariables, Runtime.ok], Runtime.modeGuard .setStart] ++
        Runtime.setFloat64Values)
      (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind])
      (by simp [parameters, CBody.bind])
    exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals)
      (RuntimeEnvironment.types_agree header objects literals) rfl
      program (Runtime.function model (signature true)) _ _ heap _ (.integer 3) 3
      defined (parameters_bound (static := ⟨literals⟩) true _ _ _ _ _)
      (BodyEmbedding.body_closed model (signature true)) (body_agrees header objects literals model)
      executed rfl behavior

theorem failure_site {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
      (input buffer : Option Address) (n m : UInt64) (references : Nat → UInt32)
      (bits : Nat → BitVec 64) (kind : Kind) (mode : Mode) (reason : Float64Set.Failure),
      program.internal.definitions (signature true).name =
        some (.tree (Runtime.function model (signature true))) →
      load heap (p.member "kind") = some (.integer kind.code) →
      load heap (p.member "mode") = some (.integer mode.code) →
      (reason = .entry → References heap input n.toNat references ∧
        Float64Set.ReadableValues heap buffer n.toNat references bits) →
      Float64Set.FailureCondition reason kind mode input buffer n m references bits →
      GuardedCalls.FailureSite program
        (.calling (signature true).name (arguments (some p) input buffer n m) heap .done)
        heap p (Float64Set.failureMessage reason) := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap p input buffer n m references bits kind mode reason defined hk hm readable condition
  obtain ⟨env, types, rest, executed, unshadowed, instanceBound⟩ :=
    Float64Set.failure_site (static := ⟨literals⟩) model
      (fragment (E := E) literals model program.internal.kernel program.addresses)
      heap p input buffer n m references bits kind mode reason
      (by simp [fragment, CCalls.Events.Program.internalOnly]) hk hm readable condition
  exact ⟨env, types, rest, reaches header objects literals model program _ heap _ defined executed,
    unshadowed, instanceBound⟩

end Rumoca.FMI3.Float64SetEnvironment
end

noncomputable section
namespace Rumoca.FMI3.Float64SetEnvironment
open CTree CMemory CBody StaticFactory CLiteral Float64Calls

/-- Every existing setter rejection, with disabled or absent logging. -/
def SuppressedContract [CInterface] (reason : Float64Set.Failure)
    (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ p input buffer n m references bits kind mode logger logging,
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (boolean logging) →
    (reason = .entry → References heap input n.toNat references ∧
      Float64Set.ReadableValues heap buffer n.toNat references bits) →
    Float64Set.FailureCondition reason kind mode input buffer n m references bits →
    (logger = none ∨ logging = false) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature true).name (arguments (some p) input buffer n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

theorem suppressed_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (reason : Float64Set.Failure) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (message : Address),
      program.internal.definitions (signature true).name =
        some (.tree (Runtime.function model (signature true))) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals (Float64Set.failureMessage reason) = some message →
      SuppressedContract reason program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap message defined helper bound p input buffer n m references bits kind mode
    logger logging hk hm hl hg readable condition suppressed behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  obtain ⟨env, types, rest, reached, unshadowed, instanceBound⟩ :=
    failure_site header objects literals model program heap p input buffer n m references bits
      kind mode reason defined hk modeLoaded readable condition
  rw [CCalls.Events.internal_prefix_behaviors program reached behavior]
  exact StaticErrors.statement_suppressed_behaviors
    ((ErrorContext.static objects literals).withRounding header) program env types rest
    (Float64Set.failureMessage reason) heap p message _ logger logging
    unshadowed instanceBound helper bound hm hl hg suppressed behavior

theorem logged_correct (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (reason : Float64Set.Failure) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program CCalls.Events.Invocation) (heap : Heap)
      (signed : Bool) (category message : Address),
      program.internal.definitions (signature true).name =
        some (.tree (Runtime.function model (signature true))) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "logStatus" = some category →
      literals (Float64Set.failureMessage reason) = some message →
      Stored signed heap category "logStatus" →
      Stored signed heap message (Float64Set.failureMessage reason) →
      Float64Set.FailureExecutionContract reason program category message heap signed := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap signed category message defined helper literal bound categoryStored messageStored
    p logger environment input buffer n m references bits kind mode name effect address external
    hk hm hl hg he readable condition
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  obtain ⟨env, types, rest, reached, unshadowed, instanceBound⟩ :=
    failure_site header objects literals model program heap p input buffer n m references bits
      kind mode reason defined hk modeLoaded readable condition
  have tail := StaticErrors.statement_all_behaviors
    ((ErrorContext.static objects literals).withRounding header) program env types rest
    (Float64Set.failureMessage reason) heap p message category logger environment _ name
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

/-- The actual setter table and diagnostic pool supply complete batched calls
on later heaps. Read-only diagnostics persist across prior host/runtime actions;
input buffers, typed writable state and callback bindings remain explicit. -/
structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  quiet : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model sigs →
      ∀ heap, Float64Set.QuietExecutionContract program heap
  failures : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool)
    (objects : Objects) (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ (category : Address) (messages : Float64Set.Failure → Address),
      pool.addresses firstBlock "logStatus" = some category ∧
      (∀ reason, pool.addresses firstBlock (Float64Set.failureMessage reason) = some (messages reason)) ∧
      Stored signed heap category "logStatus" ∧
      (∀ reason, Stored signed heap (messages reason) (Float64Set.failureMessage reason)) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : CCalls.Events.Program E),
         program.internal = LiteralPreparation.program model sigs →
         ∀ reason, SuppressedContract reason program heap) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (program : CCalls.Events.Program CCalls.Events.Invocation),
         program.internal = LiteralPreparation.program model sigs →
         ∀ reason, Float64Set.FailureExecutionContract reason program category (messages reason) heap signed)

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature true ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro program actual heap
    apply quiet_correct header objects (pool.addresses firstBlock) model program heap
    rw [actual]
    exact LiteralPreparation.function_bound model sigs unique (signature true) member
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
      (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" Logging.category_collected firstBlock
    have each : ∀ reason, ∃ message, pool.addresses firstBlock (Float64Set.failureMessage reason) = some message := by
      intro reason
      exact LiteralPreparation.message_bound model sigs made (signature true) member
        (Float64Set.failureMessage reason) (Float64Set.failure_message_collected model reason) firstBlock
    choose messages bound using each
    have categoryStored := (pool.storage_valid before firstBlock signed "logStatus" category categoryBound).preserved frame
    have messageStored := fun reason =>
      (pool.storage_valid before firstBlock signed _ (messages reason) (bound reason)).preserved frame
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    have definitions : ∀ (E : Type) (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program model sigs →
        program.internal.definitions (signature true).name =
          some (.tree (Runtime.function model (signature true))) ∧
        program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
      intro E program actual
      constructor
      · rw [actual]
        exact LiteralPreparation.function_bound model sigs unique (signature true) member
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

end Rumoca.FMI3.Float64SetEnvironment
end
