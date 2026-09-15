import RumocaFMI3.CSLoggingMemory
import RumocaFMI3.LoggingCapabilityCS
import RumocaFMI3.LoggingCapabilityEnvironment
import RumocaFMI3.LoggingRequests
import RumocaFMI3.InitializationRetention

noncomputable section

namespace Rumoca.FMI3.CSLoggingCalls
open CTree CMemory CBody StaticFactory CCalls.Events CLiteral

def next (request : DebugLogging.Request) (reference : CSRun.Reference) : CSRun.Reference :=
  if request.failed then { reference with mode := .terminated } else reference

structure Memory [CInterface] (model : Solve.Model source) (objects : Objects)
    (owners : SlotOwners.State objects.capacity) (capability : Logging.Capability) (enabled : Bool)
    (heap after : Heap) (p : Address) (buffers : StepEntry.Buffers)
    (reference : CSRun.Reference) (request : DebugLogging.Request) : Prop where
  stored : CSRun.Stored model after p buffers (next request reference)
  configuration : capability.Configured after p (request.nextLogging enabled)
  logging : after (p.member "logging") =
    InitializationProtocol.loggingCell request.loggingUpdate (heap (p.member "logging"))
  ownership : SlotOwners.Represents objects.flagsBlock after owners
  readonly : CReadOnly.Preserves heap after
  frame : ∀ q, CSRun.Protected objects buffers q → q ≠ p.member "mode" →
    q ≠ p.member "logging" → after q = heap q
  storage : ∀ region, capability.Requires (fun _ effect =>
    ∀ args before value after, effect.execute args before value after → CStorage.PreservesOn region before after) →
    CStorage.PreservesOn region heap after
  callerFrame : ∀ region : Address → Prop, capability.Requires (fun _ effect =>
    ∀ args before value after, effect.execute args before value after → ∀ q, region q → after q = before q) →
    ∀ q, region q → q ≠ p.member "mode" → q ≠ p.member "logging" → after q = heap q

theorem Memory.success [CInterface] {objects : Objects} {owners : SlotOwners.State objects.capacity}
    {capability : Logging.Capability} {request : DebugLogging.Request} {buffers : StepEntry.Buffers}
    (stored : CSRun.Stored model heap p buffers reference)
    (configured : capability.Configured heap p enabled)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (old : Option Value) (storage : heap (p.member "logging") = some ⟨.boolean, true, old⟩)
    (accepted : request.Accepted) :
    Memory model objects owners capability enabled heap (DebugLogging.written heap p request.enabled)
      p buffers reference request := by
  have memory := DebugLogging.written_storage heap p request.enabled old storage
  have frame := DebugLogging.written_frame heap p request.enabled
  have atomic := CAtomicBoolean.ordinary_store_preserves (DebugLogging.written_store heap p request.enabled old storage)
  refine ⟨?_, ?_, ?_, SlotOwners.ordinary_preserves ownership atomic,
    memory.2, (fun q _ _ different => frame q different), (fun region _ => memory.1.on region),
    fun _ _ q _ _ different => frame q different⟩
  · simpa only [next, DebugLogging.Request.failed, accepted, not_true_eq_false, decide_false, Bool.false_eq_true, if_false] using
      stored.logging_framed memory.1 frame
  · simpa only [DebugLogging.Request.nextLogging, if_pos accepted] using
      Logging.Capability.Configured.logging_written configured.1 request.enabled
  · simp [DebugLogging.written, replace, DebugLogging.Request.loggingUpdate,
      accepted, InitializationProtocol.loggingCell]

theorem Memory.failure [CInterface] {objects : Objects} {owners : SlotOwners.State objects.capacity}
    {capability : Logging.Capability} {request : DebugLogging.Request} {buffers : StepEntry.Buffers}
    (stored : CSRun.Stored model heap p buffers reference)
    (configured : capability.Configured heap p enabled)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (inPool : p.block = objects.instances.block)
    (required : capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after → CSRun.ProtectedFrame objects buffers before after))
    (rejected : ¬ request.Accepted) (events : List Invocation) (result : CBody.Result)
    (failed : capability.Failure enabled heap p category messages unknown (.terminates events result)) :
    result.value = .integer 3 ∧
    Memory model objects owners capability enabled heap result.heap p buffers reference request := by
  obtain ⟨status, nextStored, nextConfig, ownersAfter, readonly, frame⟩ :=
    CSRun.logging_failure_returned stored configured required inPool ownership events result failed
  have changed := LifecycleBodies.write_storage heap p _ .terminated stored.mode_cell
  refine ⟨status, ?_⟩
  refine ⟨?_, ?_, ?_, ownersAfter, readonly, (fun q guarded different _ => frame q guarded different), ?_, ?_⟩
  · simpa only [next, DebugLogging.Request.failed, rejected, not_false_eq_true, decide_true, if_true] using nextStored
  · simpa only [DebugLogging.Request.nextLogging, if_neg rejected] using nextConfig
  · simpa only [DebugLogging.Request.loggingUpdate, if_neg rejected, InitializationProtocol.loggingCell] using
      frame (p.member "logging") (Or.inl inPool) (by simp)
  · intro region policy
    exact (changed.1.on region).trans (Logging.Capability.Failure.storage policy events result failed)
  · intro region policy q inside different _
    have cells := (Logging.Capability.Failure.memory policy events result failed).2.2
    exact (cells q inside).trans (LifecycleBodies.write_frame heap p q .terminated different)

def CorrectObservation (request : DebugLogging.Request) (events : List Invocation) (status : Value) : Prop :=
  status = .integer (if request.failed then 3 else 0) ∧ (request.failed = false → events = [])

structure Contract [CInterface] (model : Solve.Model source) (program : Program Invocation) (objects : Objects)
    (owners : SlotOwners.State objects.capacity) (capability : Logging.Capability) (enabled : Bool)
    (heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
    (reference : CSRun.Reference) (request : DebugLogging.Request)
    (returns : List Invocation → Value → Heap → Prop) (blocked : Prop) : Prop where
  behaviors : ∀ behavior, (machine program).Behaves
    (.calling (request.call p).1 (request.call p).2 heap .done) behavior ↔
    (∃ events status after, returns events status after ∧ behavior = .terminates events ⟨status, after⟩) ∨
    (blocked ∧ behavior = .wrong [])
  available : (∃ events status after, returns events status after) ∨ blocked
  returned : ∀ events status after, returns events status after →
    CorrectObservation request events status ∧
    Memory model objects owners capability enabled heap after p buffers reference request
  failure : blocked → request.failed = true

theorem Contract.quiet [CInterface] {program : Program Invocation} {objects : Objects}
    {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}
    {request : DebugLogging.Request}
    (called : ∀ behavior, (machine program).Behaves
      (.calling (request.call p).1 (request.call p).2 heap .done) behavior ↔
      behavior = .terminates [] ⟨status, after⟩)
    (observation : CorrectObservation request [] status)
    (memory : Memory model objects owners capability enabled heap after p buffers reference request) :
    Contract model program objects owners capability enabled heap p buffers reference request
      (fun events value result => events = [] ∧ value = status ∧ result = after) False := by
  refine ⟨?_, Or.inl ⟨[], status, after, rfl, rfl, rfl⟩, ?_, False.elim⟩
  · intro behavior
    exact (called behavior).trans (by simp)
  · rintro events value result ⟨rfl, rfl, rfl⟩
    exact ⟨observation, memory⟩

/-- The same prepared public setter also preserves the CS Solve trajectory,
source epoch, clock and reusable outputs through every returning branch. -/
theorem execution (header : CFenv.Header) (objects : Objects) (model : Solve.FMI3Model source)
    (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames))
    (prepared : DebugLogging.PreparedContract model sigs pool)
    (literalBase : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation) (capability : Logging.Capability) (enabled : Bool),
      program.internal = LiteralPreparation.program model sigs →
      program.externals "strcmp" = some (CStringCalls.compareExternal (by rfl)) →
      capability.Bound program →
    ∀ (heap : Heap) (p : Address) (reference : CSRun.Reference) (buffers : StepEntry.Buffers)
      (request : DebugLogging.Request) (owners : SlotOwners.State objects.capacity),
      capability.Configured heap p enabled →
      capability.Requires (fun _ effect =>
        ∀ args before value after, effect.execute args before value after → CSRun.ProtectedFrame objects buffers before after) →
      p.block = objects.instances.block → SlotOwners.Represents objects.flagsBlock heap owners →
      CReadOnly.Preserves (pool.install literalBase firstBlock signed) heap →
      CSRun.Stored model.solve heap p buffers reference →
      request.Inputs heap → Reset.Writable heap (p.member "logging") .boolean →
      ∃ returns blocked,
        Contract model.solve program objects owners capability enabled heap p buffers reference request returns blocked := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program capability enabled actual compare bound heap p reference buffers request owners
    configured required inPool represented literals stored inputs writable
  obtain ⟨old, cell⟩ := writable
  obtain ⟨category, messages, _, _, _, _, contract⟩ :=
    Logging.Capability.prepared_request model sigs pool prepared header objects literalBase firstBlock signed
      program actual compare capability enabled heap p .cs reference.mode literals configured bound stored.mode_cell
  have call (behavior) := contract request.pointer request.count request.enabled old request.selected request.bytes
    stored.kind stored.mode inputs cell behavior
  classical
  by_cases accepted : request.Accepted
  · have called (behavior) : (machine program).Behaves
        (.calling (request.call p).1 (request.call p).2 heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, DebugLogging.written heap p request.enabled⟩ := by
      simpa only [DebugLogging.Request.call, DebugLogging.Responses, if_pos accepted.1, if_pos accepted.2] using call behavior
    refine ⟨_, False, Contract.quiet called ?_ (Memory.success stored configured represented old cell accepted)⟩
    simp [CorrectObservation, DebugLogging.Request.failed, accepted]
  · obtain ⟨unknown, rejected⟩ : ∃ unknown : Bool, ∀ behavior,
        DebugLogging.Responses heap p request.pointer request.count request.enabled request.selected request.bytes
          (capability.Failure enabled heap p category messages) behavior ↔
        capability.Failure enabled heap p category messages unknown behavior := by
      by_cases readable : request.count.toNat = 0 ∨ request.pointer.isSome = true
      · have invalid : ¬ ∀ i < request.count.toNat,
            DebugLogging.Accepted (request.selected i) (request.bytes i) (CStringMemory.content "logStatus") :=
          fun valid => accepted ⟨readable, valid⟩
        exact ⟨true, fun behavior => by simp only [DebugLogging.Responses, if_pos readable, if_neg invalid]⟩
      · exact ⟨false, fun behavior => by simp only [DebugLogging.Responses, if_neg readable]⟩
    refine ⟨(fun events status after =>
        capability.Failure enabled heap p category messages unknown (.terminates events ⟨status, after⟩)),
      capability.Failure enabled heap p category messages unknown (.wrong []), ?_⟩
    refine ⟨?_, Logging.Capability.Failure.progress capability enabled heap p category messages unknown, ?_, ?_⟩
    · intro behavior
      exact ((call behavior).trans (rejected behavior)).trans
        (Logging.Capability.Failure.cases capability enabled heap p category messages unknown behavior)
    · intro events status after returned
      obtain ⟨statusValue, memory⟩ := Memory.failure stored configured represented inPool required
        accepted events ⟨status, after⟩ returned
      refine ⟨?_, memory⟩
      simpa [CorrectObservation, DebugLogging.Request.failed, accepted] using statusValue
    · intro _
      simp [DebugLogging.Request.failed, accepted]

end Rumoca.FMI3.CSLoggingCalls

namespace Rumoca.FMI3.CSLoggingCalls
open CMemory StaticFactory

theorem Memory.retention [CInterface] {objects : Objects} {owners : SlotOwners.State objects.capacity}
    {capability : Logging.Capability} {request : DebugLogging.Request}
    (memory : Memory model objects owners capability enabled heap after p buffers reference request)
    (inPool : p.block = objects.instances.block) :
    InitializationProtocol.Retention request.loggingUpdate p heap after := by
  refine ⟨?_, memory.logging⟩
  intro name outside different
  apply memory.frame (p.member name) (Or.inl inPool) _ (by simpa using different)
  intro same
  apply outside
  have names := (Address.member_inj _ _ _).mp same
  simp [InitializationAccess.writtenFields, names]

end Rumoca.FMI3.CSLoggingCalls

end
