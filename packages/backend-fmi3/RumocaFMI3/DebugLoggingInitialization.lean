import RumocaFMI3.InitializationProtocolStorage
import RumocaFMI3.DebugLoggingLegal
import RumocaFMI3.LoggingCapabilityFrames
import RumocaFMI3.CountMemory

/-! A logging update preserves the existing initialization reference state.
The argument uses the actual public call's memory frame, rather than adding
logging data to the numerical Solve state or assuming a later valid heap. -/
noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CMemory CBody CCalls.Events StaticFactory

theorem Stored.logging_framed (stored : Stored heap p kind state)
    (storage : CStorage.Preserves heap after)
    (frame : ∀ q, q ≠ p.member "logging" → after q = heap q) :
    Stored after p kind state := by
  have field (name : String) (different : name ≠ "logging") :
      after (p.member name) = heap (p.member name) := frame _ (by simpa using different)
  refine ⟨⟨?_, (field "mode" (by decide)).trans stored.instanceStored.mode,
    (frame _ (HistoryBodies.state_ne_field p "logging")).trans stored.instanceStored.state,
    ?_⟩, stored.reset.preserved storage, ?_⟩
  · simpa only [load, field "kind" (by decide)] using stored.instanceStored.kind
  · simpa only [load, field "time" (by decide)] using stored.instanceStored.time
  · have setup {args : Initialization.Arguments} (before : Setup heap p args) : Setup after p args := by
      refine ⟨⟨(field "time" (by decide)).trans before.clock.time,
        (field "timeMin" (by decide)).trans before.clock.minimum,
        (field "eventTime" (by decide)).trans before.clock.eventTime,
        (field "lastCompleted" (by decide)).trans before.clock.lastCompleted⟩, ?_, ?_⟩
      · simpa only [load, field "stop" (by decide)] using before.stop
      · simpa only [load, field "stopDefined" (by decide)] using before.stopDefined
    cases phase : state.phase with
    | instantiated | failed => trivial
    | initializing args | initialized args =>
      have before : args.Admissible ∧ state.time = args.start ∧ Setup heap p args := by
        simpa only [phase, Phase.Configured] using stored.configured
      exact ⟨before.1, before.2.1, setup before.2.2⟩

theorem logging_legal_returned [CInterface] (program : Program Invocation)
    (stored : Stored heap p kind state)
    (contract : DebugLogging.RequestContract program heap p kind (state.phase.mode kind) failures)
    (pointer : Option Address) (count : UInt64) (enabled : Bool) (old : Option Value)
    (selected : Nat → Option Address) (bytes : Nat → List UInt8)
    (caller : pointer.isSome = true → DebugLogging.Entries heap pointer count.toNat selected bytes)
    (storage : heap (p.member "logging") = some ⟨.boolean, true, old⟩)
    (legal : DebugLogging.LegalRequest pointer count.toNat selected bytes ["logStatus"])
    (events : List Invocation) (result : CBody.Result)
    (executed : (machine program).Behaves
      (.calling DebugLogging.signature.name (DebugLogging.arguments (some p) enabled count pointer) heap .done)
      (.terminates events result)) :
    events = [] ∧ result.value = .integer 0 ∧
    load result.heap (p.member "logging") = some (boolean enabled) ∧
    Stored result.heap p kind state ∧ CStorage.Preserves heap result.heap ∧
    CReadOnly.Preserves heap result.heap ∧
    (∀ q, q ≠ p.member "logging" → result.heap q = heap q) := by
  obtain ⟨observed, status, flag, preserved, readonly, frame⟩ :=
    DebugLogging.legal_returned program heap p kind (state.phase.mode kind) failures contract
      pointer count enabled old selected bytes stored.instanceStored.kind stored.instanceStored.mode_loaded
      caller storage legal events result executed
  exact ⟨observed, status, flag, stored.logging_framed preserved frame, preserved, readonly, frame⟩

/-- Rejection enters the existing failed initialization phase. Its callback
cannot erase the numerical state, reset storage, ownership or original flag
under the universal host policy already used by initialization histories. -/
theorem logging_failure_returned [CInterface] {capability : Logging.Capability}
    (stored : Stored heap p kind state)
    (configured : capability.Configured heap p enabled)
    (required : capability.Requires (fun _ effect => Float64Rejection.Respects effect objects retained))
    (inPool : p.block = objects.instances.block)
    (owners : SlotOwners.State objects.capacity)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (events : List Invocation) (result : CBody.Result)
    (failed : capability.Failure enabled heap p category messages unknown (.terminates events result)) :
    result.value = .integer 3 ∧
    Stored result.heap p kind { state with phase := .failed } ∧
    capability.Configured result.heap p enabled ∧
    SlotOwners.Represents objects.flagsBlock result.heap owners ∧
    CallerStorage objects retained heap result.heap ∧ CReadOnly.Preserves heap result.heap ∧
    (∀ q, Float64Rejection.Protected objects retained q → q ≠ p.member "mode" → result.heap q = heap q) := by
  have preserved :
      Float64Rejection.Frame objects retained (LifecycleBodies.writeMode heap p .terminated) result.heap ∧
      CReadOnly.Preserves (LifecycleBodies.writeMode heap p .terminated) result.heap := by
    cases capability with
    | absent environment =>
      cases failed
      exact ⟨fun _ _ => rfl, .refl _⟩
    | present logger environment name effect =>
      cases enabled
      · cases failed
        exact ⟨fun _ _ => rfl, .refl _⟩
      · rcases failed with ⟨value, after, called, observed⟩ | ⟨_, impossible⟩
        · cases observed
          exact ⟨required _ _ _ _ called, effect.readonly _ _ _ _ called⟩
        · cases impossible
  obtain ⟨status, configuredAfter⟩ := Logging.Capability.Failure.returned configured
    (Logging.Capability.initialization_control required inPool) events result failed
  obtain ⟨instanceAfter, resetAfter, ownersAfter, caller, readonly, frame⟩ :=
    CountQueries.failed_memory objects retained owners heap p stored.instanceStored stored.reset
      inPool ownership preserved.1 preserved.2
  exact ⟨status, ⟨instanceAfter, resetAfter, trivial⟩, configuredAfter, ownersAfter, caller, readonly, frame⟩

end Rumoca.FMI3.InitializationProtocol
end
