import RumocaFMI3.DebugLoggingInitialization
import RumocaFMI3.LoggingCapabilityEffects

noncomputable section

namespace Rumoca.FMI3.MENumericalHistory
open CMemory CBody CCalls.Events StaticFactory

theorem Stored.logging_framed (stored : Stored heap p clock reference addresses buffer)
    (frame : ∀ q, q ≠ p.member "logging" → after q = heap q) :
    Stored after p clock reference addresses buffer := by
  have fields (name : String) (different : name ≠ "logging") :=
    frame (p.member name) (by simpa using different)
  have field (name : String) (different : name ≠ "logging") :
      load after (p.member name) = load heap (p.member name) := by
    simp only [load, fields name different]
  have state := frame (StateProofs.stateAddress p) (HistoryBodies.state_ne_field p "logging")
  obtain ⟨old, cell⟩ := stored.bufferCell
  refine ⟨⟨(field "kind" (by decide)).trans stored.control.kind,
    (fields "mode" (by decide)).trans stored.control.mode,
    ⟨(fields "time" (by decide)).trans stored.control.clockStored.time,
      (fields "timeMin" (by decide)).trans stored.control.clockStored.minimum,
      (fields "eventTime" (by decide)).trans stored.control.clockStored.eventTime,
      (fields "lastCompleted" (by decide)).trans stored.control.clockStored.lastCompleted⟩,
    stored.control.history, ?_, (field "stopDefined" (by decide)).trans stored.control.stopDefined,
    fun stop chosen => (field "stop" (by decide)).trans (stored.control.stopValue stop chosen),
    ?_, stored.control.outside⟩,
    state.trans stored.stateCell,
    ⟨old, (frame buffer (Ne.symm (stored.field_ne_buffer "logging"))).trans cell⟩,
    stored.bufferOutside, stored.bufferSeparate⟩
  · simpa only [StateProofs.Represents, load, state] using stored.control.modelStored
  · apply stored.control.buffers.transport
    intro layout member
    exact frame _ (stored.control.outside.field layout member "logging")

/-- The setter preserves the importer's current ME trial state and control
clock. This does not assert that an external integrator solves the source IVP. -/
theorem logging_legal_returned [CInterface] (program : Program Invocation)
    (stored : Stored heap p clock reference addresses buffer)
    (contract : DebugLogging.RequestContract program heap p .me reference.control.mode failures)
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
    Stored result.heap p clock reference addresses buffer ∧ CStorage.Preserves heap result.heap ∧
    CReadOnly.Preserves heap result.heap ∧
    (∀ q, q ≠ p.member "logging" → result.heap q = heap q) := by
  obtain ⟨observed, status, flag, preserved, readonly, frame⟩ :=
    DebugLogging.legal_returned program heap p .me reference.control.mode failures contract
      pointer count enabled old selected bytes stored.control.kind stored.mode_loaded
      caller storage legal events result executed
  exact ⟨observed, status, flag, stored.logging_framed frame, preserved, readonly, frame⟩

theorem logging_failure_returned [CInterface] {capability : Logging.Capability}
    {owners : SlotOwners.State objects.capacity}
    (stored : Stored heap p clock reference addresses buffer)
    (reset : Reset.Storage heap p)
    (configured : capability.Configured heap p enabled)
    (required : capability.Requires (fun _ effect => MEFailure.Respects effect objects addresses buffer))
    (inPool : p.block = objects.instances.block)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (events : List Invocation) (result : CBody.Result)
    (failed : capability.Failure enabled heap p category messages unknown (.terminates events result)) :
    result.value = .integer 3 ∧
    Stored result.heap p clock reference.failed addresses buffer ∧ Reset.Storage result.heap p ∧
    capability.Configured result.heap p enabled ∧
    SlotOwners.Represents objects.flagsBlock result.heap owners ∧
    CReadOnly.Preserves heap result.heap ∧
    (∀ q, MEFailure.Protected objects addresses buffer q → q ≠ p.member "mode" → result.heap q = heap q) := by
  obtain ⟨status, readonly, frame⟩ := Logging.Capability.Failure.memory required events result failed
  have callbackFrame : MEFailure.ProtectedFrame objects addresses buffer
      (LifecycleBodies.writeMode heap p .terminated) result.heap := frame
  have numerical := callbackFrame.numerical inPool
  have changed := LifecycleBodies.write_storage heap p _ .terminated stored.control.mode
  obtain ⟨_, configuredAfter⟩ := Logging.Capability.Failure.returned configured
    (Logging.Capability.me_control required inPool) events result failed
  exact ⟨status, stored.failed.framed numerical,
    numerical.reset_storage (stored.failed_reset reset), configuredAfter,
    callbackFrame.owners (SlotOwners.ordinary_preserves ownership changed.2.2),
    changed.2.1.trans readonly,
    fun q inside different => (callbackFrame q inside).trans
      (LifecycleBodies.write_frame heap p q .terminated different)⟩

end Rumoca.FMI3.MENumericalHistory

end
