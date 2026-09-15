import RumocaFMI3.InitializationProtocolRejection
import RumocaFMI3.DiscreteEvaluationRequests
import RumocaFMI3.CountMemory

/-! Evaluation interleaves with the existing initialization protocol. Calls
derive success or rejection, with the same ownership, borrowing and complete
modeled callback outcomes. Successful evaluation cannot complete event iteration. -/
noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CMemory CBody StaticFactory CCalls.Events CLiteral

variable {objects : Objects} {owners : SlotOwners.State objects.capacity}

theorem evaluation_call [CInterface] (model : Solve.FMI3Model source)
    (program : Program Invocation) (quiet : DiscreteEvaluation.QuietContract program)
    (stored : Stored heap p kind state)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (allowed : Reference.Allowed .evaluateDiscrete kind (state.phase.mode kind)) :
    CallContract model program objects retained owners p buffers heap kind state (.evaluation .evaluate) := by
  have called := quiet.successful heap p kind (state.phase.mode kind)
    stored.instanceStored.kind stored.instanceStored.mode_loaded allowed
  exact CallContract.quiet rfl called rfl
    (Result.ordinary stored ownership (.refl _) (.refl _) (.refl _)
      (fun _ _ => rfl) rfl (fun _ _ _ => rfl))

theorem Result.evaluation_rejected
    (stored : Stored heap p kind state)
    (inPool : p.block = objects.instances.block)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (callbackFrame : Float64Rejection.Frame objects retained (LifecycleBodies.writeMode heap p .terminated) after)
    (callbackReadonly : CReadOnly.Preserves (LifecycleBodies.writeMode heap p .terminated) after) :
    Result objects retained owners p buffers heap after kind state (.evaluation .reject) := by
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

theorem evaluation_rejection_call
    (header : CFenv.Header) (objects : Objects)
    (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames))
    (prepared : DiscreteEvaluation.PreparedContract model sigs pool)
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation), program.internal = LiteralPreparation.program model sigs →
    ∀ (heap : Heap) (p : Address) (buffers : Float64Buffers.Layout) (kind : Kind) (state : State)
      (owners : SlotOwners.State objects.capacity) (retained : Address → Prop),
      CReadOnly.Preserves (pool.install baseHeap firstBlock signed) heap →
      Stored heap p kind state → (¬ Reference.Allowed .evaluateDiscrete kind (state.phase.mode kind)) →
      p.block = objects.instances.block → SlotOwners.Represents objects.flagsBlock heap owners →
      LogPolicy program objects retained heap p →
      CallContract model program objects retained owners p buffers heap kind state (.evaluation .reject) := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual heap p buffers kind state owners retained literals stored condition inPool ownership policy
  obtain ⟨category, message, _, _, _, _, quiet, logged⟩ :=
    prepared.failures header baseHeap firstBlock signed objects heap literals
  have behavior (observed) :
      (Action.evaluation .reject).Behaves program heap p buffers observed ↔
      (machine program).Behaves (.calling DiscreteEvaluation.signature.name
        (DiscreteEvaluation.arguments (some p)) heap .done) observed := by
    simp [Action.Behaves, Action.hostRun, Action.call, DiscreteEvaluation.Request.call]
  rcases policy.current with ⟨logger, logging, loggerValue, loggingValue, suppressed⟩ |
    ⟨logger, environment, name, effect, loggerValue, loggingValue, environmentValue, address, external, respects⟩
  · have called := fun observed => (behavior observed).trans
      (quiet Invocation program actual p kind (state.phase.mode kind) logger logging
        stored.instanceStored.kind stored.instanceStored.mode loggerValue loggingValue suppressed condition observed)
    refine ⟨Or.inl ⟨[], .integer 3, _, (called _).mpr rfl⟩, ?_⟩
    intro observed status after executed
    have same := (called _).mp executed
    cases same
    exact ⟨⟨rfl, rfl⟩, Result.evaluation_rejected stored inPool ownership
      (fun _ _ => rfl) (.refl _)⟩
  · obtain ⟨called, _⟩ := logged program actual p logger environment kind (state.phase.mode kind)
      name effect address external stored.instanceStored.kind stored.instanceStored.mode
      loggerValue loggingValue environmentValue condition
    have outcomes := fun observed => (behavior observed).trans (called observed)
    refine ⟨?_, ?_⟩
    · classical
      by_cases returns : ∃ value after, effect.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) value after
      · obtain ⟨value, after, returned⟩ := returns
        exact Or.inl ⟨[⟨name, Logging.arguments environment category message⟩], .integer 3, after,
          (outcomes _).mpr (Or.inl ⟨value, after, returned, rfl⟩)⟩
      · exact Or.inr ((outcomes _).mpr (Or.inr ⟨fun value after returned => returns ⟨value, after, returned⟩, rfl⟩))
    · intro observed status after executed
      rcases (outcomes _).mp executed with ⟨value, actualAfter, callback, same⟩ | ⟨_, impossible⟩
      · have equal : observed = [⟨name, Logging.arguments environment category message⟩] ∧
            status = .integer 3 ∧ after = actualAfter := by
          simpa only [Transition.Events.Observation.terminates.injEq, CBody.Result.mk.injEq] using same
        obtain ⟨_, returnedStatus, sameAfter⟩ := equal
        subst actualAfter
        exact ⟨⟨returnedStatus, rfl⟩, Result.evaluation_rejected stored inPool ownership
          (respects _ _ _ _ callback) (effect.readonly _ _ _ _ callback)⟩
      · cases impossible

end Rumoca.FMI3.InitializationProtocol
end
