import RumocaFMI3.InitializationProtocolRejection
import RumocaFMI3.DebugLoggingInitialization
import RumocaFMI3.LoggingCapabilityEnvironment

/-! Logging requests execute in the existing initialization protocol. The
prepared public C contract determines every raw status, flag update and error
transition, including a callback with no modeled return. -/
noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CMemory CBody StaticFactory CCalls.Events CLiteral

theorem logging_call (request : DebugLogging.Request) (header : CFenv.Header) (objects : Objects)
    (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames))
    (prepared : DebugLogging.PreparedContract model sigs pool)
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation), program.internal = LiteralPreparation.program model sigs →
    program.externals "strcmp" = some (CStringCalls.compareExternal (by rfl)) →
    ∀ (heap : Heap) (p : Address) (buffers : Float64Buffers.Layout) (kind : Kind) (state : State)
      (owners : SlotOwners.State objects.capacity) (retained : Address → Prop),
      CReadOnly.Preserves (pool.install baseHeap firstBlock signed) heap →
      Stored heap p kind state → request.Inputs heap →
      p.block = objects.instances.block → SlotOwners.Represents objects.flagsBlock heap owners →
      LogPolicy program objects retained heap p →
      CallContract model program objects retained owners p buffers heap kind state (.logging request) := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual compare heap p buffers kind state owners retained readonly stored inputs inPool ownership policy
  obtain ⟨capability, enabled, configured, bound, required, old, writable⟩ := policy
  obtain ⟨category, messages, _, _, _, _, contract⟩ :=
    Logging.Capability.prepared_request model sigs pool prepared header objects baseHeap firstBlock signed
      program actual compare capability enabled heap p kind (state.phase.mode kind) readonly configured bound stored.instanceStored.mode
  have call (observed) :
      (Action.logging request).Behaves program heap p buffers observed ↔
      DebugLogging.Responses heap p request.pointer request.count request.enabled request.selected request.bytes
        (capability.Failure enabled heap p category messages) observed := by
    have behavior : (Action.logging request).Behaves program heap p buffers observed ↔
        (machine program).Behaves (.calling DebugLogging.signature.name
          (DebugLogging.arguments (some p) request.enabled request.count request.pointer) heap .done) observed := by
      simp [Action.Behaves, Action.hostRun, Action.call, DebugLogging.Request.call]
    exact behavior.trans (contract request.pointer request.count request.enabled old request.selected request.bytes
      stored.instanceStored.kind stored.instanceStored.mode_loaded inputs writable observed)
  classical
  by_cases accepted : request.Accepted
  · have calls (observed) : (Action.logging request).Behaves program heap p buffers observed ↔
        observed = .terminates [] ⟨.integer 0, DebugLogging.written heap p request.enabled⟩ := by
      simpa only [DebugLogging.Responses, if_pos accepted.1, if_pos accepted.2] using call observed
    refine ⟨Or.inl ⟨[], .integer 0, _, (calls _).mpr rfl⟩, ?_⟩
    intro events status after executed
    have same := (calls _).mp executed
    cases same
    have memory := DebugLogging.written_storage heap p request.enabled old writable
    have frame := DebugLogging.written_frame heap p request.enabled
    have atomic := CAtomicBoolean.ordinary_store_preserves (DebugLogging.written_store heap p request.enabled old writable)
    refine ⟨?_, ?_⟩
    · simp [Action.Observed, DebugLogging.Request.failed, accepted, Action.readback, Float64Access.Observation.ok]
    · refine ⟨?_, SlotOwners.ordinary_preserves ownership atomic, CallerStorage.ordinary memory.1,
        memory.2, ?_, ?_⟩
      · simpa only [Action.next, DebugLogging.Request.failed, accepted, not_true_eq_false, decide_false, Bool.false_eq_true,
          if_false] using stored.logging_framed memory.1 frame
      · simpa only [Action.loggingUpdate, DebugLogging.Request.loggingUpdate, if_pos accepted] using
          Retention.logging_written heap p request.enabled
      · intro q _ outside _ _
        exact frame q (fun same => outside (same ▸ p.member_in_record "logging"))
  · obtain ⟨unknown, rejected⟩ : ∃ unknown : Bool, ∀ observed,
        DebugLogging.Responses heap p request.pointer request.count request.enabled request.selected request.bytes
          (capability.Failure enabled heap p category messages) observed ↔
        capability.Failure enabled heap p category messages unknown observed := by
      by_cases readable : request.count.toNat = 0 ∨ request.pointer.isSome = true
      · have invalid : ¬ ∀ i < request.count.toNat,
            DebugLogging.Accepted (request.selected i) (request.bytes i) (CStringMemory.content "logStatus") :=
          fun valid => accepted ⟨readable, valid⟩
        exact ⟨true, fun observed => by simp only [DebugLogging.Responses, if_pos readable, if_neg invalid]⟩
      · exact ⟨false, fun observed => by simp only [DebugLogging.Responses, if_neg readable]⟩
    have calls := fun observed => (call observed).trans (rejected observed)
    refine ⟨?_, ?_⟩
    · rcases Logging.Capability.Failure.progress capability enabled heap p category messages unknown with
        ⟨events, status, after, returned⟩ | stopped
      · exact Or.inl ⟨events, status, after, (calls _).mpr returned⟩
      · exact Or.inr ((calls _).mpr stopped)
    · intro events status after executed
      obtain ⟨statusValue, instanceAfter, _, ownersAfter, caller, immutable, frame⟩ :=
        logging_failure_returned stored configured required inPool owners ownership events ⟨status, after⟩
          ((calls _).mp executed)
      refine ⟨?_, ?_⟩
      · simp only [Action.Observed, DebugLogging.Request.failed, accepted, not_false_eq_true,
          decide_true, if_true, Action.readback]
        exact ⟨statusValue, trivial⟩
      · refine ⟨?_, ownersAfter, caller, immutable, ?_, ?_⟩
        · simpa only [Action.next, DebugLogging.Request.failed, accepted, not_false_eq_true,
            decide_true, if_true] using instanceAfter
        · have retainedFields : Retains p heap after := by
            intro name outside
            apply frame (p.member name) (Or.inl inPool)
            intro same
            apply outside
            have equal := (Address.member_inj _ _ _).mp same
            simp [InitializationAccess.writtenFields, equal]
          simpa only [Action.loggingUpdate, DebugLogging.Request.loggingUpdate, if_neg accepted] using
            Retention.of_retains retainedFields
        · intro q guarded outside _ _
          exact frame q guarded (fun same => outside (same ▸ p.member_in_record "mode"))

end Rumoca.FMI3.InitializationProtocol
end
