import RumocaFMI3.InitializationProtocolCalls

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CMemory CBody StaticFactory CCalls.Events CLiteral

/-- A stored logger is either suppressed or bound to an observed external
effect with a universal frame. No callback return or determinism is assumed. -/
def LogPolicy [CInterface] (program : Program Invocation) (objects : Objects) (retained : Address → Prop)
    (heap : Heap) (p : Address) : Prop :=
  (∃ (logger : Option Address) (logging : Bool),
    load heap (p.member "logger") = some (.pointer logger) ∧
    load heap (p.member "logging") = some (boolean logging) ∧ (logger = none ∨ logging = false)) ∨
  (∃ (logger : Address) (environment : Option Address) (name : String) (effect : ReturningEffect (Logging.signature name)),
    load heap (p.member "logger") = some (.pointer (some logger)) ∧
    load heap (p.member "logging") = some (.integer 1) ∧
    load heap (p.member "environment") = some (.pointer environment) ∧
    program.addresses logger = some name ∧
    program.externals name = some (External.observed (Logging.signature name) effect) ∧
    Float64Rejection.Respects effect objects retained)

theorem LogPolicy.fields [CInterface] {program : Program Invocation}
    (policy : LogPolicy program objects retained heap p)
    (frame : ∀ name ∈ ["logger", "logging", "environment"], after (p.member name) = heap (p.member name)) :
    LogPolicy program objects retained after p := by
  have field (name : String) (member : name ∈ ["logger", "logging", "environment"]) :
      load after (p.member name) = load heap (p.member name) := by simp only [load, frame name member]
  rcases policy with ⟨logger, logging, loggerValue, loggingValue, quiet⟩ |
    ⟨logger, environment, name, effect, loggerValue, loggingValue, environmentValue, address, external, respects⟩
  · exact Or.inl ⟨logger, logging, (field "logger" (by decide)).trans loggerValue,
      (field "logging" (by decide)).trans loggingValue, quiet⟩
  · exact Or.inr ⟨logger, environment, name, effect, (field "logger" (by decide)).trans loggerValue,
      (field "logging" (by decide)).trans loggingValue, (field "environment" (by decide)).trans environmentValue,
      address, external, respects⟩

theorem LogPolicy.framed [CInterface] {program : Program Invocation}
    (policy : LogPolicy program objects retained heap p) (frame : Retains p heap after) :
    LogPolicy program objects retained after p := by
  apply policy.fields
  intro name member
  apply frame
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide

variable {objects : Objects} {owners : SlotOwners.State objects.capacity}

theorem Result.rejection
    (returned : Float64Rejection.Returned objects retained owners request heap p kind state.value state.time after)
    (inPool : p.block = objects.instances.block) (separate : ∀ q, p.InRecord q → request.Outside q) :
    Result objects retained owners p buffers heap after kind state (.reject request) := by
  refine ⟨Stored.rejected returned, returned.ownership, returned.storage, returned.readonly, ?_, ?_⟩
  · intro name outside
    apply returned.frame (p.member name) (Or.inl inPool) (separate _ (p.member_in_record name))
    intro same
    apply outside
    have equal := (Address.member_inj _ _ _).mp same
    simp [InitializationAccess.writtenFields, equal]
  · intro q guarded notRecord _ outside
    exact returned.frame q guarded outside (fun same => notRecord (same ▸ p.member_in_record "mode"))

theorem rejection_call (request : Float64Rejection.Request) (header : CFenv.Header) (objects : Objects)
    (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames))
    (getter : Float64Environment.PreparedContract model sigs pool)
    (setter : Float64SetEnvironment.PreparedContract model sigs pool)
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation), program.internal = LiteralPreparation.program model sigs →
    ∀ (heap : Heap) (p : Address) (buffers : Float64Buffers.Layout) (kind : Kind) (state : State)
      (owners : SlotOwners.State objects.capacity) (retained : Address → Prop),
      CReadOnly.Preserves (pool.install baseHeap firstBlock signed) heap →
      Stored heap p kind state → request.TransferStorage heap →
      (∀ q, p.InRecord q → request.Outside q) → request.Condition kind (state.phase.mode kind) →
      p.block = objects.instances.block → SlotOwners.Represents objects.flagsBlock heap owners →
      LogPolicy program objects retained heap p →
      CallContract model program objects retained owners p buffers heap kind state (.reject request) := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual heap p buffers kind state owners retained literals stored inputs separate condition inPool ownership policy
  obtain ⟨category, message, _, _, _, quiet, logged⟩ :=
    request.execution header objects model sigs pool getter setter baseHeap firstBlock signed program actual
      heap p kind _ state.value state.time owners retained literals stored.instanceStored stored.reset inputs separate condition inPool ownership
  rcases policy with ⟨logger, logging, loggerValue, loggingValue, suppressed⟩ |
    ⟨logger, environment, name, effect, loggerValue, loggingValue, environmentValue, address, external, respects⟩
  · obtain ⟨called, returned⟩ := quiet logger logging loggerValue loggingValue suppressed
    refine ⟨Or.inl ⟨[], .integer 3, _, (called _).mpr rfl⟩, ?_⟩
    intro events status after executed
    have same := (called _).mp executed
    cases same
    exact ⟨⟨rfl, rfl⟩, Result.rejection returned inPool separate⟩
  · obtain ⟨called, completed⟩ := logged logger environment name effect loggerValue loggingValue environmentValue address external respects
    refine ⟨?_, ?_⟩
    · classical
      by_cases returns : ∃ value after, effect.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (request.prepare heap) p .terminated) value after
      · obtain ⟨value, after, returned⟩ := returns
        exact Or.inl ⟨[⟨name, Logging.arguments environment category message⟩], .integer 3, after,
          (called _).mpr (Or.inl ⟨value, after, returned, rfl⟩)⟩
      · exact Or.inr ((called _).mpr (Or.inr ⟨fun value after returned => returns ⟨value, after, returned⟩, rfl⟩))
    · intro events status after executed
      obtain ⟨_, returnedStatus, returned⟩ := completed events status after executed
      exact ⟨⟨returnedStatus, rfl⟩, Result.rejection returned inPool separate⟩

end Rumoca.FMI3.InitializationProtocol
end
