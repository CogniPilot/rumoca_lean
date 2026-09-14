import RumocaFMI3.StaticErrorCalls
import RumocaFMI3.InitializationContract

/-! Complete initialization and error contracts in the static object
environment, derived from the same emitted definitions and diagnostics. -/
noncomputable section
namespace Rumoca.FMI3.StaticInitialization
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory

theorem enter_silent_correct {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (reason : InitializationCalls.Failure) (program : CCalls.Events.Program E)
      (message : Address) (heap : Heap),
      program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals (InitializationCalls.failureMessage reason) = some message →
      InitializationCalls.SilentExecutionContract reason program heap := by
  letI : CInterface := executionInterface objects literals
  intro reason program message heap defined helper messageBound p args kind mode logger hk hm hl hg condition behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have certified := InitializationCalls.failure_prefix (static := ⟨literals⟩) heap p args kind mode reason hk modeLoaded condition
  exact StaticErrors.failure_silent_behaviors (ErrorContext.static objects literals) program InitializationCalls.function
    (InitializationCalls.arguments (some p) args) heap heap p message (InitializationCalls.failureMessage reason)
    _ logger (enter_agrees objects literals) certified defined helper messageBound hm hl hg behavior

theorem enter_logged_correct (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (reason : InitializationCalls.Failure) (program : CCalls.Events.Program Invocation)
      (category message : Address) (heap : Heap) (signed : Bool),
      program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "logStatus" = some category → literals (InitializationCalls.failureMessage reason) = some message →
      Stored signed heap category "logStatus" → Stored signed heap message (InitializationCalls.failureMessage reason) →
      InitializationCalls.FailureExecutionContract reason program category message heap signed := by
  letI : CInterface := executionInterface objects literals
  intro reason program category message heap signed defined helper literal messageBound categoryStored messageStored
    p logger environment args kind mode name effect address external hk hm hl hg he condition
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have certified := InitializationCalls.failure_prefix (static := ⟨literals⟩) heap p args kind mode reason hk modeLoaded condition
  have all := StaticErrors.failure_all_behaviors (ErrorContext.static objects literals) program InitializationCalls.function
    (InitializationCalls.arguments (some p) args) heap heap p message category logger
    (InitializationCalls.failureMessage reason) name environment _
    (External.observed (Logging.signature name) effect) (enter_agrees objects literals) certified defined helper
    messageBound address external rfl literal hm hl hg he
  constructor
  · intro behavior
    exact (all behavior).trans (observed_choices effect _ _ (fun _ after => ⟨.integer 3, after⟩) behavior)
  · intro value after executed
    have successful := (all (.terminates [⟨name, Logging.arguments environment category message⟩]
      ⟨.integer 3, after⟩)).mpr (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := CCalls.Events.termination_preserves successful
    exact ⟨categoryStored.preserved preserved, messageStored.preserved preserved⟩

theorem exit_silent_correct {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (message : Address) (heap : Heap),
      program.internal.definitions InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals ErrorCalls.rejectionMessage = some message →
      InitializationExit.SilentExecutionContract program heap := by
  letI : CInterface := executionInterface objects literals
  intro program message heap defined helper messageBound p kind mode logger hk hm hl hg denied behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have certified := InitializationExit.failure_prefix (static := ⟨literals⟩) model heap p kind mode hk modeLoaded denied
  exact StaticErrors.failure_silent_behaviors (ErrorContext.static objects literals) program (Runtime.function model InitializationExit.signature)
    (InitializationExit.arguments (some p)) heap heap p message ErrorCalls.rejectionMessage
    _ logger (exit_agrees model objects literals) certified defined helper messageBound hm hl hg behavior

theorem exit_logged_correct (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program Invocation) (category message : Address) (heap : Heap) (signed : Bool),
      program.internal.definitions InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "logStatus" = some category → literals ErrorCalls.rejectionMessage = some message →
      Stored signed heap category "logStatus" → Stored signed heap message ErrorCalls.rejectionMessage →
      InitializationExit.FailureExecutionContract program category message heap signed := by
  letI : CInterface := executionInterface objects literals
  intro program category message heap signed defined helper literal messageBound categoryStored messageStored
    p logger environment kind mode name effect address external hk hm hl hg he denied
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have certified := InitializationExit.failure_prefix (static := ⟨literals⟩) model heap p kind mode hk modeLoaded denied
  have all := StaticErrors.failure_all_behaviors (ErrorContext.static objects literals) program (Runtime.function model InitializationExit.signature)
    (InitializationExit.arguments (some p)) heap heap p message category logger ErrorCalls.rejectionMessage name environment _
    (External.observed (Logging.signature name) effect) (exit_agrees model objects literals) certified defined helper
    messageBound address external rfl literal hm hl hg he
  constructor
  · intro behavior
    exact (all behavior).trans (observed_choices effect _ _ (fun _ after => ⟨.integer 3, after⟩) behavior)
  · intro value after executed
    have successful := (all (.terminates [⟨name, Logging.arguments environment category message⟩]
      ⟨.integer 3, after⟩)).mpr (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := CCalls.Events.termination_preserves successful
    exact ⟨categoryStored.preserved preserved, messageStored.preserved preserved⟩

def SuppressedEntryContract [interface : CInterface] (reason : InitializationCalls.Failure)
    (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ (p : Address) (args : InitializationCalls.Raw) (kind : Kind) (mode : Mode)
    (logger : Option Address) (logging : Bool),
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (boolean logging) →
    (logger = none ∨ logging = false) → InitializationCalls.FailureCondition reason mode args →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling InitializationCalls.signature.name (InitializationCalls.arguments (some p) args) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

def SuppressedExitContract [interface : CInterface]
    (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ (p : Address) (kind : Kind) (mode : Mode) (logger : Option Address) (logging : Bool),
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (boolean logging) →
    (logger = none ∨ logging = false) → mode ≠ .initialization →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

theorem enter_suppressed_correct {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (reason : InitializationCalls.Failure) (program : CCalls.Events.Program E)
      (message : Address) (heap : Heap),
      program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals (InitializationCalls.failureMessage reason) = some message →
      SuppressedEntryContract reason program heap := by
  letI : CInterface := executionInterface objects literals
  intro reason program message heap defined helper messageBound
    p args kind mode logger logging hk hm hl hg suppressed condition behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have certified := InitializationCalls.failure_prefix (static := ⟨literals⟩) heap p args kind mode reason hk modeLoaded condition
  exact StaticErrors.failure_suppressed_behaviors (ErrorContext.static objects literals) program InitializationCalls.function
    (InitializationCalls.arguments (some p) args) heap heap p message (InitializationCalls.failureMessage reason)
    _ logger logging (enter_agrees objects literals) certified defined helper messageBound hm hl hg suppressed behavior

theorem exit_suppressed_correct {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (message : Address) (heap : Heap),
      program.internal.definitions InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals ErrorCalls.rejectionMessage = some message → SuppressedExitContract program heap := by
  letI : CInterface := executionInterface objects literals
  intro program message heap defined helper messageBound p kind mode logger logging hk hm hl hg suppressed denied behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have certified := InitializationExit.failure_prefix (static := ⟨literals⟩) model heap p kind mode hk modeLoaded denied
  exact StaticErrors.failure_suppressed_behaviors (ErrorContext.static objects literals) program (Runtime.function model InitializationExit.signature)
    (InitializationExit.arguments (some p)) heap heap p message ErrorCalls.rejectionMessage
    _ logger logging (exit_agrees model objects literals) certified defined helper messageBound hm hl hg suppressed behavior

/-- Complete admitted and rejected initialization calls share the prepared
literal pool and actual table with static creation. The heap may contain the
writes of earlier calls, provided it retains the immutable diagnostics. -/
def PreparedContract (model : Solve.FMI3Model source) (signatures : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model signatures).flatMap functionNames)) : Prop :=
  ∀ (before : Heap) (firstBlock : Nat) (signed : Bool) (objects : Objects) (heap : Heap),
    CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ (category : Address) (messages : InitializationCalls.Failure → Address),
      pool.addresses firstBlock "logStatus" = some category ∧ Stored signed heap category "logStatus" ∧
      (∀ reason, pool.addresses firstBlock (InitializationCalls.failureMessage reason) = some (messages reason) ∧
        Stored signed heap (messages reason) (InitializationCalls.failureMessage reason)) ∧
      (letI : CInterface := executionInterface objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : CCalls.Events.Program E),
         program.internal = LiteralPreparation.program model signatures →
         InitializationCalls.QuietExecutionContract program ∧
         (∀ reason, InitializationCalls.SilentExecutionContract reason program heap) ∧
         InitializationExit.SilentExecutionContract program heap ∧
         (∀ reason, SuppressedEntryContract reason program heap) ∧ SuppressedExitContract program heap) ∧
      (letI : CInterface := executionInterface objects (pool.addresses firstBlock)
       ∀ (program : CCalls.Events.Program Invocation),
         program.internal = LiteralPreparation.program model signatures →
         (∀ reason, InitializationCalls.FailureExecutionContract reason program category (messages reason) heap signed) ∧
         InitializationExit.FailureExecutionContract program category (messages .lifecycle) heap signed)

theorem prepared_correct (model : Solve.FMI3Model source) (signatures : List Signature)
    (unique : ((LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name)).Nodup)
    (contract : InitializationCalls.FunctionContract model signatures enterText exitText)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model signatures).flatMap functionNames)}
    (made : LiteralPreparation.prepare model signatures = some pool) :
    PreparedContract model signatures pool := by
  intro before firstBlock signed objects heap frame
  obtain ⟨category, messages, categoryBound, categoryInitial, each, _, _⟩ :=
    contract.prepared pool made before firstBlock signed
  have categoryStored := categoryInitial.preserved frame
  have messageStored := fun reason => (each reason).2.preserved frame
  let literals := pool.addresses firstBlock
  letI : CInterface := executionInterface objects literals
  have definitions : ∀ (E : Type) (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model signatures →
      program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) ∧
      program.internal.definitions InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) ∧
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
    intro E program actual
    refine ⟨?_, ?_, ?_⟩
    · rw [actual, ← InitializationCalls.function_eq model]
      exact LiteralPreparation.function_bound model signatures unique _ contract.enterMember
    · rw [actual]
      exact LiteralPreparation.function_bound model signatures unique _ contract.exitMember
    · rw [actual]
      exact LiteralPreparation.helpers_bound model signatures Runtime.helpers[0] (by simp [Runtime.helpers])
  refine ⟨category, messages, categoryBound, categoryStored,
    fun reason => ⟨(each reason).1, messageStored reason⟩, ?_, ?_⟩
  · intro E program actual
    obtain ⟨enterDefined, exitDefined, helper⟩ := definitions E program actual
    exact ⟨quiet_correct objects literals model program enterDefined exitDefined,
      fun reason => enter_silent_correct objects literals reason program _ heap enterDefined helper (each reason).1,
      exit_silent_correct objects literals model program _ heap exitDefined helper (each .lifecycle).1,
      fun reason => enter_suppressed_correct objects literals reason program _ heap enterDefined helper (each reason).1,
      exit_suppressed_correct objects literals model program _ heap exitDefined helper (each .lifecycle).1⟩
  · intro program actual
    obtain ⟨enterDefined, exitDefined, helper⟩ := definitions Invocation program actual
    exact ⟨fun reason => enter_logged_correct objects literals reason program category (messages reason) heap signed
      enterDefined helper categoryBound (each reason).1 categoryStored (messageStored reason),
      exit_logged_correct objects literals model program category (messages .lifecycle) heap signed
      exitDefined helper categoryBound (each .lifecycle).1 categoryStored (messageStored .lifecycle)⟩

end Rumoca.FMI3.StaticInitialization
