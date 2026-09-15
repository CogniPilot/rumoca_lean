import RumocaFMI3.DebugLoggingInitialization
import RumocaFMI3.CSRunFinish
import RumocaFMI3.CSRunLogging
import RumocaFMI3.LoggingCapabilityCS
import RumocaFMI3.LoggingCapabilityEffects

noncomputable section

namespace Rumoca.FMI3.CSRun
open CMemory CBody CCalls.Events StaticFactory

theorem Stored.logging_framed {buffers : StepEntry.Buffers}
    (stored : Stored model heap p buffers reference)
    (storage : CStorage.Preserves heap after)
    (frame : ∀ q, q ≠ p.member "logging" → after q = heap q) :
    Stored model after p buffers reference := by
  have field (name : String) (different : name ≠ "logging") :
      after (p.member name) = heap (p.member name) := frame _ (by simpa using different)
  have loaded (name : String) (different : name ≠ "logging") :
      load after (p.member name) = load heap (p.member name) := by
    simp only [load, field name different]
  have writable {address type} (cell : Reset.Writable heap address type) :
      Reset.Writable after address type := by
    obtain ⟨old, found⟩ := cell
    exact storage.cell found
  exact ⟨(loaded "kind" (by decide)).trans stored.kind,
    (loaded "mode" (by decide)).trans stored.mode,
    (field "time" (by decide)).trans stored.clock,
    (frame _ (HistoryBodies.state_ne_field p "logging")).trans stored.state,
    (loaded "stopDefined" (by decide)).trans stored.stopDefined,
    fun limit chosen => (loaded "stop" (by decide)).trans (stored.stopValue limit chosen),
    stored.reset.preserved storage,
    ⟨writable stored.buffers.event, writable stored.buffers.terminate,
      writable stored.buffers.early, writable stored.buffers.last,
      stored.buffers.outsideEvent, stored.buffers.outsideTerminate,
      stored.buffers.outsideEarly, stored.buffers.outsideLast⟩⟩

/-- Every returned legal public call leaves the same Solve run and rounded
communication clock, while changing the logging flag to the requested value. -/
theorem logging_legal_returned [CInterface] {buffers : StepEntry.Buffers} (program : Program Invocation)
    (stored : Stored model heap p buffers reference)
    (contract : DebugLogging.RequestContract program heap p .cs reference.mode failures)
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
    Stored model result.heap p buffers reference ∧ CStorage.Preserves heap result.heap ∧
    CReadOnly.Preserves heap result.heap ∧
    (∀ q, q ≠ p.member "logging" → result.heap q = heap q) := by
  obtain ⟨observed, status, flag, preserved, readonly, frame⟩ :=
    DebugLogging.legal_returned program heap p .cs reference.mode failures contract
      pointer count enabled old selected bytes stored.kind stored.mode caller storage legal events result executed
  exact ⟨observed, status, flag, stored.logging_framed preserved frame, preserved, readonly, frame⟩

/-- A logging error terminates the lifecycle without altering the completed
Solve trajectory, its source epoch, rounded clock or reusable output storage. -/
theorem Stored.failed {buffers : StepEntry.Buffers}
    (stored : Stored model heap p buffers reference) :
    Stored model (LifecycleBodies.writeMode heap p .terminated) p buffers
      { reference with mode := .terminated } := by
  have fields (name : String) (different : name ≠ "mode") :=
    LifecycleBodies.write_frame heap p (p.member name) .terminated (by simpa using different)
  have field (name : String) (different : name ≠ "mode") :
      load (LifecycleBodies.writeMode heap p .terminated) (p.member name) = load heap (p.member name) := by
    simp only [load, fields name different]
  have changed := LifecycleBodies.write_storage heap p _ .terminated stored.mode_cell
  have writable {address type} (cell : Reset.Writable heap address type) :
      Reset.Writable (LifecycleBodies.writeMode heap p .terminated) address type := by
    obtain ⟨old, found⟩ := cell
    exact changed.1.cell found
  refine ⟨(field "kind" (by decide)).trans stored.kind, ?_,
    (fields "time" (by decide)).trans stored.clock,
    (LifecycleBodies.write_frame heap p _ .terminated
      (HistoryBodies.state_ne_field p "mode")).trans stored.state,
    (field "stopDefined" (by decide)).trans stored.stopDefined,
    fun limit chosen => (field "stop" (by decide)).trans (stored.stopValue limit chosen),
    stored.reset.preserved changed.1,
    ⟨writable stored.buffers.event, writable stored.buffers.terminate,
      writable stored.buffers.early, writable stored.buffers.last,
      stored.buffers.outsideEvent, stored.buffers.outsideTerminate,
      stored.buffers.outsideEarly, stored.buffers.outsideLast⟩⟩
  simp [load, LifecycleBodies.writeMode, Mode.code, replace, convert]

theorem logging_failure_returned [CInterface] {capability : Logging.Capability}
    {buffers : StepEntry.Buffers} {owners : SlotOwners.State objects.capacity}
    (stored : Stored model heap p buffers reference)
    (configured : capability.Configured heap p enabled)
    (required : capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after →
        ProtectedFrame objects buffers before after))
    (inPool : p.block = objects.instances.block)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (events : List Invocation) (result : CBody.Result)
    (failed : capability.Failure enabled heap p category messages unknown (.terminates events result)) :
    result.value = .integer 3 ∧
    Stored model result.heap p buffers { reference with mode := .terminated } ∧
    capability.Configured result.heap p enabled ∧
    SlotOwners.Represents objects.flagsBlock result.heap owners ∧
    CReadOnly.Preserves heap result.heap ∧
    (∀ q, Protected objects buffers q → q ≠ p.member "mode" → result.heap q = heap q) := by
  obtain ⟨status, readonly, frame⟩ := Logging.Capability.Failure.memory required events result failed
  have callbackFrame : ProtectedFrame objects buffers (LifecycleBodies.writeMode heap p .terminated) result.heap := frame
  have changed := LifecycleBodies.write_storage heap p _ .terminated stored.mode_cell
  obtain ⟨_, configuredAfter⟩ := Logging.Capability.Failure.returned configured
    (Logging.Capability.cs_control required inPool) events result failed
  exact ⟨status, stored.failed.framed (callbackFrame.run inPool), configuredAfter,
    callbackFrame.owners (SlotOwners.ordinary_preserves ownership changed.2.2),
    changed.2.1.trans readonly,
    fun q inside different => (callbackFrame q inside).trans
      (LifecycleBodies.write_frame heap p q .terminated different)⟩

end Rumoca.FMI3.CSRun

end
