import RumocaFMI3.InitializationProtocolRejection
import RumocaFMI3.NominalMemory
import RumocaFMI3.CountMemory

/-! Nominal observations share the existing raw initialization protocol.
Original caller storage supplies every later request; modeled logger outcomes
are retained without assuming the callback returns. -/
noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CMemory CBody StaticFactory CCalls.Events CLiteral

variable {objects : Objects} {owners : SlotOwners.State objects.capacity}

theorem nominal_get_call [CInterface] (model : Solve.FMI3Model source)
    (program : Program Invocation)
    (quiet : ∀ heap, Nominals.QuietExecutionContract program heap)
    (stored : Stored heap p kind state)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (buffer : Address) (old : Option Value)
    (storage : heap buffer = some ⟨.float64, true, old⟩)
    (separate : ¬ p.InRecord buffer)
    (allowed : Reference.Allowed .getNominals kind (state.phase.mode kind)) :
    CallContract model program objects retained owners p buffers heap kind state (.nominals (.get buffer)) := by
  have called := (quiet heap).successful p buffer kind (state.phase.mode kind) old
    stored.instanceStored.kind stored.instanceStored.mode_loaded allowed storage
  obtain ⟨instanceAfter, resetAfter, ownersAfter, preserved, readonly, _, frame⟩ :=
    Nominals.written_memory heap p buffer kind (state.phase.mode kind) state.value state.time
      objects owners old storage stored.instanceStored stored.reset ownership separate
  have record (q : Address) (inside : p.InRecord q) : Nominals.written heap buffer q = heap q :=
    frame q (fun same => separate (same ▸ inside))
  have observation := NominalAccess.Request.get_observed model (Nominals.stored heap buffer)
  refine CallContract.quiet rfl called ?_ ?_
  · simp only [Action.Observed, NominalAccess.Request.failed, Bool.false_eq_true, ↓reduceIte,
      Action.readback, observation, Float64Access.Observation.ok]
  · exact ⟨⟨instanceAfter, resetAfter, stored.configured.framed
        (fun name _ => record _ (p.member_in_record name))⟩,
      ownersAfter, CallerStorage.ordinary preserved, readonly,
      Retention.of_retains (fun name _ => record _ (p.member_in_record name)), fun q _ _ _ outside => frame q outside⟩

theorem Result.nominal_rejected (access : Bool) (buffer : Option Address) (count : UInt64)
    (stored : Stored heap p kind state)
    (inPool : p.block = objects.instances.block)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (callbackFrame : Float64Rejection.Frame objects retained (LifecycleBodies.writeMode heap p .terminated) after)
    (callbackReadonly : CReadOnly.Preserves (LifecycleBodies.writeMode heap p .terminated) after) :
    Result objects retained owners p buffers heap after kind state (.nominals (.reject access buffer count)) := by
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

theorem nominal_rejection_call (access : Bool) (buffer : Option Address) (count : UInt64)
    (header : CFenv.Header) (objects : Objects)
    (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames))
    (prepared : NominalEnvironment.PreparedContract model sigs pool)
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation), program.internal = LiteralPreparation.program model sigs →
    ∀ (heap : Heap) (p : Address) (buffers : Float64Buffers.Layout) (kind : Kind) (state : State)
      (owners : SlotOwners.State objects.capacity) (retained : Address → Prop),
      CReadOnly.Preserves (pool.install baseHeap firstBlock signed) heap →
      Stored heap p kind state → Nominals.FailureCondition access kind (state.phase.mode kind) buffer count →
      p.block = objects.instances.block → SlotOwners.Represents objects.flagsBlock heap owners →
      LogPolicy program objects retained heap p →
      CallContract model program objects retained owners p buffers heap kind state (.nominals (.reject access buffer count)) := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual heap p buffers kind state owners retained literals stored condition inPool ownership policy
  obtain ⟨category, messages, _, _, _, _, quiet, logged⟩ :=
    prepared.failures header baseHeap firstBlock signed objects heap literals
  have behavior (observed) :
      (Action.nominals (.reject access buffer count)).Behaves program heap p buffers observed ↔
      (machine program).Behaves (.calling ErrorCalls.nominalSignature.name
        (ErrorCalls.nominalArguments p buffer count) heap .done) observed := by
    simp [Action.Behaves, Action.hostRun, Action.call, NominalAccess.Request.call]
  rcases policy.current with ⟨logger, logging, loggerValue, loggingValue, suppressed⟩ |
    ⟨logger, environment, name, effect, loggerValue, loggingValue, environmentValue, address, external, respects⟩
  · have called := fun observed => (behavior observed).trans
      (quiet Invocation program actual access p buffer count kind (state.phase.mode kind) logger logging
        stored.instanceStored.kind stored.instanceStored.mode loggerValue loggingValue condition suppressed observed)
    refine ⟨Or.inl ⟨[], .integer 3, _, (called _).mpr rfl⟩, ?_⟩
    intro observed status after executed
    have same := (called _).mp executed
    cases same
    exact ⟨⟨rfl, rfl⟩, Result.nominal_rejected access buffer count stored inPool ownership
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
        exact ⟨⟨returnedStatus, rfl⟩, Result.nominal_rejected access buffer count stored inPool ownership
          (respects _ _ _ _ callback) (effect.readonly _ _ _ _ callback)⟩
      · cases impossible

end Rumoca.FMI3.InitializationProtocol
end
