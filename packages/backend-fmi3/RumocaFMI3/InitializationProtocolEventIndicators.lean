import RumocaFMI3.InitializationProtocolRejection
import RumocaFMI3.EventIndicatorRequests
import RumocaFMI3.CountMemory

/-! Empty event-indicator queries participate in the same initialization
protocol. Success does not touch output memory; failure retains every modeled
logger return and the blocked alternative. -/
noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CMemory CBody StaticFactory CCalls.Events CLiteral

variable {objects : Objects} {owners : SlotOwners.State objects.capacity}

theorem event_indicators_get_call [CInterface] (model : Solve.FMI3Model source)
    (program : Program Invocation)
    (quiet : ∀ heap, EventIndicatorCalls.QuietContract program heap)
    (stored : Stored heap p kind state)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (buffer : Option Address)
    (allowed : EventIndicatorCalls.Allowed kind (state.phase.mode kind)) :
    CallContract model program objects retained owners p buffers heap kind state (.eventIndicators (.get buffer)) := by
  have called := (quiet heap).get_refines p buffer kind (state.phase.mode kind)
    stored.instanceStored.kind stored.instanceStored.mode_loaded allowed
  exact CallContract.quiet rfl called rfl
    (Result.ordinary stored ownership (.refl _) (.refl _) (.refl _)
      (fun _ _ => rfl) rfl (fun _ _ _ => rfl))

theorem Result.event_indicators_rejected (access : Bool) (buffer : Option Address) (count : UInt64)
    (stored : Stored heap p kind state)
    (inPool : p.block = objects.instances.block)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (callbackFrame : Float64Rejection.Frame objects retained (LifecycleBodies.writeMode heap p .terminated) after)
    (callbackReadonly : CReadOnly.Preserves (LifecycleBodies.writeMode heap p .terminated) after) :
    Result objects retained owners p buffers heap after kind state (.eventIndicators (.reject access buffer count)) := by
  obtain ⟨instanceAfter, resetAfter, ownersAfter, preserved, readonly, frame⟩ :=
    CountQueries.failed_memory objects retained owners heap p stored.instanceStored stored.reset
      inPool ownership callbackFrame callbackReadonly
  refine ⟨⟨instanceAfter, resetAfter, trivial⟩, ownersAfter, preserved, readonly, Retention.of_retains ?_, ?_⟩
  · intro name outside
    apply frame (p.member name) (Or.inl inPool)
    intro same
    apply outside
    have equal := (Address.member_inj _ _ _).mp same
    simp [InitializationAccess.writtenFields, equal]
  · intro q guarded notRecord _ _
    exact frame q guarded (fun same => notRecord (same ▸ p.member_in_record "mode"))

theorem event_indicators_rejection_call (access : Bool) (buffer : Option Address) (count : UInt64)
    (header : CFenv.Header) (objects : Objects)
    (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames))
    (prepared : EventIndicatorEnvironment.PreparedContract model sigs pool)
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation), program.internal = LiteralPreparation.program model sigs →
    ∀ (heap : Heap) (p : Address) (buffers : Float64Buffers.Layout) (kind : Kind) (state : State)
      (owners : SlotOwners.State objects.capacity) (retained : Address → Prop),
      CReadOnly.Preserves (pool.install baseHeap firstBlock signed) heap →
      Stored heap p kind state → EventIndicatorCalls.FailureCondition access kind (state.phase.mode kind) count →
      p.block = objects.instances.block → SlotOwners.Represents objects.flagsBlock heap owners →
      LogPolicy program objects retained heap p →
      CallContract model program objects retained owners p buffers heap kind state (.eventIndicators (.reject access buffer count)) := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual heap p buffers kind state owners retained literals stored condition inPool ownership policy
  obtain ⟨category, messages, _, _, _, _, quiet, logged⟩ :=
    prepared.failures header baseHeap firstBlock signed objects heap literals
  have behavior (observed) :
      (Action.eventIndicators (.reject access buffer count)).Behaves program heap p buffers observed ↔
      (machine program).Behaves (.calling EventIndicatorCalls.signature.name
        (EventIndicatorCalls.values (some p) buffer count) heap .done) observed := by
    simp [Action.Behaves, Action.hostRun, Action.call, EventIndicatorAccess.Request.call]
  rcases policy.current with ⟨logger, logging, loggerValue, loggingValue, suppressed⟩ |
    ⟨logger, environment, name, effect, loggerValue, loggingValue, environmentValue, address, external, respects⟩
  · have called := fun observed => (behavior observed).trans
      (quiet Invocation program actual access p buffer count kind (state.phase.mode kind) logger logging
        stored.instanceStored.kind stored.instanceStored.mode loggerValue loggingValue condition suppressed observed)
    refine ⟨Or.inl ⟨[], .integer 3, _, (called _).mpr rfl⟩, ?_⟩
    intro observed status after executed
    have same := (called _).mp executed
    cases same
    exact ⟨⟨rfl, rfl⟩, Result.event_indicators_rejected access buffer count stored inPool ownership
      (fun _ _ => rfl) (.refl _)⟩
  · obtain ⟨called, _⟩ := logged program actual access p logger environment buffer count kind (state.phase.mode kind)
      name effect address external stored.instanceStored.kind stored.instanceStored.mode
      loggerValue loggingValue environmentValue condition
    have outcomes := fun observed => (behavior observed).trans (called observed)
    refine ⟨?_, ?_⟩
    · classical
      by_cases returns : ∃ value after, effect.execute (Logging.arguments environment category (messages access))
          (LifecycleBodies.writeMode heap p .terminated) value after
      · obtain ⟨value, after, returned⟩ := returns
        exact Or.inl ⟨[⟨name, Logging.arguments environment category (messages access)⟩], .integer 3, after,
          (outcomes _).mpr (Or.inl ⟨value, after, returned, rfl⟩)⟩
      · exact Or.inr ((outcomes _).mpr (Or.inr ⟨fun value after returned => returns ⟨value, after, returned⟩, rfl⟩))
    · intro observed status after executed
      rcases (outcomes _).mp executed with ⟨value, actualAfter, callback, same⟩ | ⟨_, impossible⟩
      · have equal : observed = [⟨name, Logging.arguments environment category (messages access)⟩] ∧
            status = .integer 3 ∧ after = actualAfter := by
          simpa only [Transition.Events.Observation.terminates.injEq, CBody.Result.mk.injEq] using same
        obtain ⟨_, returnedStatus, sameAfter⟩ := equal
        subst actualAfter
        exact ⟨⟨returnedStatus, rfl⟩, Result.event_indicators_rejected access buffer count stored inPool ownership
          (respects _ _ _ _ callback) (effect.readonly _ _ _ _ callback)⟩
      · cases impossible

end Rumoca.FMI3.InitializationProtocol
end
