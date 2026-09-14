import RumocaFMI3.InitializationProtocolRejection
import RumocaFMI3.CountMemory

/-! Count observations use the existing initialization execution relation.
Success preserves the model and writes one caller cell; failure retains every
modeled logger outcome and derives the storage needed for a later reset. -/
noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CMemory CBody StaticFactory CCalls.Events CLiteral

variable {objects : Objects} {owners : SlotOwners.State objects.capacity}

theorem count_get_call [CInterface] (model : Solve.FMI3Model source)
    (program : Program Invocation) (events : Bool)
    (quiet : ∀ heap, CountEnvironment.QuietContract events program heap)
    (stored : Stored heap p kind state)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (buffer : Address) (old : Option Value)
    (storage : heap buffer = some ⟨.size, true, old⟩)
    (separate : ¬ p.InRecord buffer)
    (allowed : Reference.Allowed .getCounts kind (state.phase.mode kind)) :
    CallContract model program objects retained owners p buffers heap kind state (.counts (.get events buffer)) := by
  have called := (quiet heap).successful p buffer kind (state.phase.mode kind) old
    stored.instanceStored.kind stored.instanceStored.mode_loaded allowed storage
  obtain ⟨instanceAfter, resetAfter, ownersAfter, preserved, readonly, _, frame⟩ :=
    CountQueries.written_memory events heap p buffer kind (state.phase.mode kind) state.value state.time
      objects owners old storage stored.instanceStored stored.reset ownership separate
  have record (q : Address) (inside : p.InRecord q) : CountQueries.written events heap buffer q = heap q :=
    frame q (fun same => separate (same ▸ inside))
  have observation := (quiet heap).returned model p buffer kind (state.phase.mode kind) old
    stored.instanceStored.kind stored.instanceStored.mode_loaded allowed storage [] _ ((called _).mpr rfl)
  refine CallContract.quiet rfl called ?_ ?_
  · simp only [Action.Observed, CountAccess.Request.failed, Bool.false_eq_true, ↓reduceIte,
      Action.readback, CountAccess.Request.readback, CountAccess.Request.expected,
      observation.2.2.1, Float64Access.Observation.ok]
  · exact ⟨⟨instanceAfter, resetAfter, stored.configured.framed
        (fun name _ => record _ (p.member_in_record name))⟩,
      ownersAfter, CallerStorage.ordinary preserved, readonly,
      fun name _ => record _ (p.member_in_record name), fun q _ _ _ outside => frame q outside⟩

theorem Result.count_rejected (events missing : Bool) (buffer : Option Address)
    (stored : Stored heap p kind state)
    (inPool : p.block = objects.instances.block)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (callbackFrame : Float64Rejection.Frame objects retained (LifecycleBodies.writeMode heap p .terminated) after)
    (callbackReadonly : CReadOnly.Preserves (LifecycleBodies.writeMode heap p .terminated) after) :
    Result objects retained owners p buffers heap after kind state (.counts (.reject events missing buffer)) := by
  obtain ⟨instanceAfter, resetAfter, ownersAfter, preserved, readonly, frame⟩ :=
    CountQueries.failed_memory objects retained owners heap p stored.instanceStored stored.reset
      inPool ownership callbackFrame callbackReadonly
  refine ⟨⟨instanceAfter, resetAfter, trivial⟩, ownersAfter, preserved, readonly, ?_, ?_⟩
  · intro name outside
    apply frame (p.member name) (Or.inl inPool)
    intro same
    apply outside
    have equal := (Address.member_inj _ _ _).mp same
    simp [InitializationAccess.writtenFields, equal]
  · intro q guarded notRecord _ _
    exact frame q guarded (fun same => notRecord (same ▸ p.member_in_record "mode"))

theorem count_rejection_call (events missing : Bool) (buffer : Option Address)
    (header : CFenv.Header) (objects : Objects)
    (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames))
    (prepared : CountEnvironment.PreparedContract model sigs events pool)
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation), program.internal = LiteralPreparation.program model sigs →
    ∀ (heap : Heap) (p : Address) (buffers : Float64Buffers.Layout) (kind : Kind) (state : State)
      (owners : SlotOwners.State objects.capacity) (retained : Address → Prop),
      CReadOnly.Preserves (pool.install baseHeap firstBlock signed) heap →
      Stored heap p kind state → CountQueries.FailureCondition missing kind (state.phase.mode kind) buffer →
      p.block = objects.instances.block → SlotOwners.Represents objects.flagsBlock heap owners →
      LogPolicy program objects retained heap p →
      CallContract model program objects retained owners p buffers heap kind state (.counts (.reject events missing buffer)) := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual heap p buffers kind state owners retained literals stored condition inPool ownership policy
  obtain ⟨category, messages, _, _, _, _, quiet, logged⟩ :=
    prepared.failures header baseHeap firstBlock signed objects heap literals
  have behavior (observed) :
      (Action.counts (.reject events missing buffer)).Behaves program heap p buffers observed ↔
      (machine program).Behaves (.calling (CountQueries.signature events).name
        (CountQueries.arguments (some p) buffer) heap .done) observed := by
    simp [Action.Behaves, Action.hostRun, Action.call, CountAccess.Request.call]
  rcases policy with ⟨logger, logging, loggerValue, loggingValue, suppressed⟩ |
    ⟨logger, environment, name, effect, loggerValue, loggingValue, environmentValue, address, external, respects⟩
  · have called := fun observed => (behavior observed).trans
      (quiet Invocation program actual missing p buffer kind (state.phase.mode kind) logger logging
        stored.instanceStored.kind stored.instanceStored.mode loggerValue loggingValue condition suppressed observed)
    refine ⟨Or.inl ⟨[], .integer 3, _, (called _).mpr rfl⟩, ?_⟩
    intro observed status after executed
    have same := (called _).mp executed
    cases same
    exact ⟨⟨rfl, rfl⟩, Result.count_rejected events missing buffer stored inPool ownership
      (fun _ _ => rfl) (.refl _)⟩
  · obtain ⟨called, _⟩ := logged program actual missing p logger environment buffer kind (state.phase.mode kind)
      name effect address external stored.instanceStored.kind stored.instanceStored.mode
      loggerValue loggingValue environmentValue condition
    have outcomes := fun observed => (behavior observed).trans (called observed)
    refine ⟨?_, ?_⟩
    · classical
      by_cases returns : ∃ value after, effect.execute (Logging.arguments environment category (messages missing))
          (LifecycleBodies.writeMode heap p .terminated) value after
      · obtain ⟨value, after, returned⟩ := returns
        exact Or.inl ⟨[⟨name, Logging.arguments environment category (messages missing)⟩], .integer 3, after,
          (outcomes _).mpr (Or.inl ⟨value, after, returned, rfl⟩)⟩
      · exact Or.inr ((outcomes _).mpr (Or.inr ⟨fun value after returned => returns ⟨value, after, returned⟩, rfl⟩))
    · intro observed status after executed
      rcases (outcomes _).mp executed with ⟨value, actualAfter, callback, same⟩ | ⟨_, impossible⟩
      · have equal : observed = [⟨name, Logging.arguments environment category (messages missing)⟩] ∧
            status = .integer 3 ∧ after = actualAfter := by
          simpa only [Transition.Events.Observation.terminates.injEq, CBody.Result.mk.injEq] using same
        obtain ⟨_, returnedStatus, sameAfter⟩ := equal
        subst actualAfter
        exact ⟨⟨returnedStatus, rfl⟩, Result.count_rejected events missing buffer stored inPool ownership
          (respects _ _ _ _ callback) (effect.readonly _ _ _ _ callback)⟩
      · cases impossible

end Rumoca.FMI3.InitializationProtocol
end
