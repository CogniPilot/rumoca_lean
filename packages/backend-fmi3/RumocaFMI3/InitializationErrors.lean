import RumocaFMI3.InitializationFailures
import RumocaFMI3.LoggingContract
import RumocaC.ObservedCalls

noncomputable section
namespace Rumoca.FMI3.InitializationCalls
open Initialization
open CTree CMemory CLiteral CCalls.Events

def FailureExecutionContract [interface : CInterface] (reason : Failure)
    (program : CCalls.Events.Program Invocation) (category message : Address) (heap : Heap) (signed : Bool) : Prop :=
  ∀ (p logger : Address) (environment : Option Address) (args : Raw) (kind : Kind) (mode : Mode)
    (name : String) (effect : ReturningEffect (Logging.signature name)),
    program.addresses logger = some name →
    program.externals name = some (External.observed (Logging.signature name) effect) →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    FailureCondition reason mode args →
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) args) heap .done) behavior ↔
      (∃ value after, effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after ∧
        behavior = .terminates [⟨name, Logging.arguments environment category message⟩] ⟨.integer 3, after⟩) ∨
      ((∀ value after, ¬ effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after) ∧ behavior = .wrong [])) ∧
    (∀ value after, effect.execute (Logging.arguments environment category message)
      (LifecycleBodies.writeMode heap p .terminated) value after →
      Stored signed after category "logStatus" ∧ Stored signed after message (failureMessage reason))

def SilentExecutionContract [interface : CInterface] (reason : Failure)
    (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ (p : Address) (args : Raw) (kind : Kind) (mode : Mode) (logger : Option Address),
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (.integer 0) →
    FailureCondition reason mode args →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) args) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem failure_execution_correct (reason : Failure)
    (program : CCalls.Events.Program Invocation) (category message : Address) (heap : Heap) (signed : Bool)
    (defined : program.internal.definitions signature.name = some (.tree function))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (literal : static.addresses "logStatus" = some category)
    (messageBound : static.addresses (failureMessage reason) = some message)
    (categoryStored : Stored signed heap category "logStatus")
    (messageStored : Stored signed heap message (failureMessage reason)) :
    FailureExecutionContract reason program category message heap signed := by
  intro p logger environment args kind mode name effect address external hk hm hl hg he condition
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have certified := failure_prefix heap p args kind mode reason hk modeLoaded condition
  have all := GuardedCalls.FailurePrefix.all_behaviors program function (arguments (some p) args)
    heap heap p message category logger (failureMessage reason) name environment _
    (External.observed (Logging.signature name) effect) certified defined helper messageBound
    address external rfl literal hm hl hg he
  constructor
  · intro behavior
    exact (all behavior).trans (observed_choices effect _ _ (fun _ after => ⟨.integer 3, after⟩) behavior)
  · intro value after executed
    have successful := (all (.terminates [⟨name, Logging.arguments environment category message⟩]
      ⟨.integer 3, after⟩)).mpr (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := CCalls.Events.termination_preserves successful
    exact ⟨categoryStored.preserved preserved, messageStored.preserved preserved⟩

theorem silent_execution_correct (reason : Failure)
    (program : CCalls.Events.Program E) (message : Address) (heap : Heap)
    (defined : program.internal.definitions signature.name = some (.tree function))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses (failureMessage reason) = some message) :
    SilentExecutionContract reason program heap := by
  intro p args kind mode logger hk hm hl hg condition behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have certified := failure_prefix heap p args kind mode reason hk modeLoaded condition
  exact GuardedCalls.FailurePrefix.silent_behaviors program function (arguments (some p) args)
    heap heap p message (failureMessage reason) _ logger certified defined helper messageBound hm hl hg behavior

theorem time_guard (heap : Heap) (p : Address) (args : Initialization.Arguments)
    (admissible : Arguments.Admissible args) (time : Binary64.Value) :
    CBody.eval (TimeProofs.locals p (Binary64.toBits time).val)
      (InitializationEntry.finalHeap heap p args) Runtime.invalidTime = some (CBody.boolean false) ↔
      (Time.Window.initial args.start args.stopTime).Admissible time := by
  apply HistoryProofs.stored_guard_reference (InitializationEntry.finalHeap heap p args) p
    (Time.Clock.initial args.start) (Time.History.initial args.start args.stopTime) time
    (stored heap p args) (Time.initial_represents args.start args.stopTime)
  · simpa only [Time.History.initial, Time.Window.initial, stopTime_defined args admissible]
      using (InitializationEntry.stop heap p args).2
  · intro bound hb
    have hbits := stopTime_bits args admissible bound hb
    simpa only [Value.finite, hbits] using (InitializationEntry.stop heap p args).1

end
end Rumoca.FMI3.InitializationCalls
