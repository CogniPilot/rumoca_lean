import RumocaFMI3.MEMixedRun

noncomputable section
namespace Rumoca.FMI3.MEMixedRun
open CTree CMemory CBody StaticFactory CCalls.Events

/-- A successful numerical action or restart retains its complete call
certificate, all observations and the deterministic reference clock. -/
theorem run_correct (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : Program Invocation), MEEnvironment.Quiet model program → StaticReset.ExecutionContract program →
      program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
      program.internal.definitions InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) →
      ∀ heap p clock reference addresses buffer action,
      MENumericalHistory.Stored heap p clock reference addresses buffer → Reset.Storage heap p →
      (Action.run action).Allowed buffer clock reference →
      ∃ after epochs, MENumericalRun.Calls program p addresses buffer heap [action]
        (MENumericalRun.observations model reference [action]) after epochs ∧
        MENumericalHistory.Stored after p ((Action.run action).clock clock) ((Action.run action).next reference) addresses buffer ∧
        Reset.Storage after p ∧ CReadOnly.Preserves heap after ∧ CAtomicBoolean.Preserves heap after ∧
        CStorage.Preserves heap after ∧
        (∀ q, MENumericalRun.Outside p addresses buffer q → after q = heap q) := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program quiet reset enterDefined exitDefined heap p clock reference addresses buffer action stored storage allowed
  cases action with
  | numerical command =>
    obtain ⟨prepared, called, nextStored, output, controls, readonly, frame⟩ :=
      MENumericalHistory.step program quiet stored command allowed
    exact ⟨_, [], .numerical (.cons prepared called output controls .nil) .nil, nextStored,
      MENumericalHistory.step_reset_storage model command stored nextStored storage, readonly,
      MENumericalHistory.action_atomic model stored command,
      MENumericalHistory.action_storage model stored command, fun q outside => frame q outside.1⟩
  | restart args =>
    have recovery := MEFailure.Recovery.correct header objects literals model program reset enterDefined exitDefined
      heap p clock reference addresses buffer args stored storage allowed
    exact ⟨_, _, recovery.calls, recovery.stored, recovery.resetStorage, recovery.readonly, recovery.atomic,
      MENumericalHistory.restart_storage model stored storage args allowed,
      fun q outside => MENumericalRun.restart_frame heap p args outside⟩

/-- Every admitted action supplies the full target contract and invariants
for every returning branch, from its original storage and logger configuration. -/
theorem action_correct (header : CFenv.Header) (objects : Objects) (model : Solve.FMI3Model source)
    (sigs : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap CLiteral.functionNames))
    (prepared : MEEnvironment.PreparedContract model sigs pool)
    (counts : ∀ events, CountEnvironment.PreparedContract model sigs events pool)
    (literalBase : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation) (config : Configuration),
      program.internal = LiteralPreparation.program model sigs →
      StaticReset.ExecutionContract program →
      program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
      program.internal.definitions InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) →
      ∀ heap p clock reference addresses buffer action (owners : SlotOwners.State objects.capacity),
      config.Valid program objects addresses buffer → config.Stored heap p →
      p.block = objects.instances.block → SlotOwners.Represents objects.flagsBlock heap owners →
      CReadOnly.Preserves (pool.install literalBase firstBlock signed) heap →
      MENumericalHistory.Stored heap p clock reference addresses buffer → Reset.Storage heap p →
      action.Allowed buffer clock reference →
      action.Prepared objects heap addresses buffer →
      ∃ returns blocked, ActionContract program p addresses buffer heap action returns blocked ∧
        ∀ observed after epochs, returns observed after epochs →
          Returned model objects owners config p addresses buffer heap after reference clock action observed := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program config actual reset enterDefined exitDefined heap p clock reference addresses buffer action owners
    valid configured inPool represented literals stored storage allowed ready
  have configuration (after : Heap)
      (frame : ∀ q, MEFailure.Protected objects addresses buffer q → MENumericalRun.Outside p addresses buffer q → after q = heap q) :
      config.Stored after p := by
    apply configured.framed
    intro name member
    exact frame _ (Or.inl inPool) (configuration_outside stored name (by simpa using List.mem_append_left ["slot"] member))
  cases action with
  | counts request =>
    obtain ⟨outcomes, blocked, contract⟩ := MECountCalls.execution header objects model sigs pool counts
      literalBase firstBlock signed program config actual heap p clock reference addresses buffer request owners
      valid configured inPool represented literals stored storage ready.1 ready.2 allowed
    refine ⟨_, blocked, .counts contract, ?_⟩
    rintro observed after epochs ⟨events, status, rfl, rfl, returned⟩
    obtain ⟨observation, memory⟩ := contract.returned events status after returned
    refine ⟨memory.stored, memory.reset, memory.configuration, memory.ownership, ?_, memory.readonly,
      fun q guarded outside => memory.frame q guarded outside.1.1.2.1, memory.storage⟩
    cases request with
    | get which output =>
      obtain ⟨statusEq, quiet, readback⟩ := observation
      have empty := quiet rfl
      simp only [Action.Observed, statusEq, empty, readback, CountAccess.Request.failed,
        Bool.false_eq_true, ↓reduceIte, MENumericalHistory.Observation.ok]
    | reject which missing output =>
      exact ⟨events, by simp only [CountAccess.Request.readback, observation.1,
        CountAccess.Request.failed, ↓reduceIte]⟩
  | run command =>
    obtain ⟨after, epochs, called, nextStored, nextReset, readonly, atomic, keptStorage, frame⟩ :=
      run_correct header objects (pool.addresses firstBlock) model program
        (prepared.quiet header Invocation objects firstBlock program actual) reset enterDefined exitDefined
        heap p clock reference addresses buffer command stored storage allowed
    refine ⟨_, False, .run called, ?_⟩
    rintro observed next checkpoints ⟨rfl, rfl, rfl⟩
    exact ⟨nextStored, nextReset, configuration _ (fun q _ outside => frame q outside),
      SlotOwners.ordinary_preserves represented atomic, rfl, readonly, (fun q _ outside => frame q outside),
      fun region _ => keptStorage.on region⟩
  | reject request input =>
    obtain ⟨preparation, readyStored, readyReset, readyReadonly, readyAtomic⟩ := MEFailure.prepare_correct input stored storage
    let ready := MEFailure.prepare input heap buffer
    have readyStorage := preparation.storage
    have condition := MEFailure.Request.Selected.condition allowed readyStored
    obtain ⟨category, message, _, _, _, _, silent, logged⟩ :=
      request.prepared prepared header literalBase firstBlock signed objects ready (literals.trans readyReadonly)
    have readyOwners := SlotOwners.ordinary_preserves represented readyAtomic
    have readyConfig : config.Stored ready p := by
      apply configured.framed
      intro name _
      exact MEFailure.prepare_frame input heap buffer _ (stored.field_ne_buffer name)
    have finishFrame (after : Heap)
        (frame : ∀ q, MEFailure.Protected objects addresses buffer q → q ≠ p.member "mode" → after q = ready q) :
        ∀ q, MEFailure.Protected objects addresses buffer q → MENumericalRun.Outside p addresses buffer q → after q = heap q := by
      intro q guarded outside
      exact (frame q guarded outside.1.1.2.1).trans (MEFailure.prepare_frame input heap buffer q outside.1.2.2)
    cases config with
    | quiet logger logging =>
      have called := silent Invocation program actual p .me reference.control.mode logger logging
        readyStored.control.kind readyStored.control.mode condition readyConfig.1 readyConfig.2 valid
      have frame := finishFrame _ (fun q _ other => LifecycleBodies.write_frame ready p q .terminated other)
      refine ⟨_, False, .quiet preparation called, ?_⟩
      rintro observed after epochs ⟨rfl, rfl, rfl⟩
      exact ⟨readyStored.failed, readyStored.failed_reset readyReset, configuration _ frame,
        SlotOwners.ordinary_preserves readyOwners readyStored.failed_atomic, ⟨[], rfl⟩,
        readyReadonly.trans (termination_preserves ((called _).mpr rfl)), frame,
        fun region _ => (readyStorage.trans (CStorage.replace_typed readyStored.control.mode
          ⟨.int32, true, some (.integer Mode.terminated.code)⟩ rfl rfl)).on region⟩
    | logged logger environment name effect =>
      obtain ⟨address, external, policy⟩ := valid
      have called := (logged program actual p logger environment .me reference.control.mode name effect address external
        readyStored.control.kind readyStored.control.mode condition readyConfig.1 readyConfig.2.1 readyConfig.2.2).1
      refine ⟨_, _, .logged name effect (Logging.arguments environment category message) preparation called, ?_⟩
      rintro observed after epochs ⟨rfl, rfl, value, outcome⟩
      obtain ⟨nextStored, nextReset, nextOwners, preserved⟩ := policy.returned readyStored readyReset inPool readyOwners outcome
      have frame := finishFrame after preserved
      exact ⟨nextStored, nextReset, configuration after frame, nextOwners, ⟨_, rfl⟩,
        readyReadonly.trans (termination_preserves ((called _).mpr (Or.inl ⟨value, after, outcome, rfl⟩))), frame,
        fun region preserve =>
          ((readyStorage.trans (CStorage.replace_typed readyStored.control.mode
            ⟨.int32, true, some (.integer Mode.terminated.code)⟩ rfl rfl)).on region).trans
            (preserve _ _ _ _ outcome)⟩

/-- Arbitrarily long finite mixtures retain all modeled callback outcomes.
No later heap, expected status or returning callback is supplied as a premise. -/
theorem trace_correct (header : CFenv.Header) (objects : Objects) (model : Solve.FMI3Model source)
    (sigs : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap CLiteral.functionNames))
    (prepared : MEEnvironment.PreparedContract model sigs pool)
    (counts : ∀ events, CountEnvironment.PreparedContract model sigs events pool)
    (literalBase : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation) (config : Configuration),
      program.internal = LiteralPreparation.program model sigs →
      StaticReset.ExecutionContract program →
      program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
      program.internal.definitions InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) →
      ∀ heap p clock reference final finalClock addresses buffer actions (owners : SlotOwners.State objects.capacity),
      config.Valid program objects addresses buffer → config.Stored heap p →
      p.block = objects.instances.block → SlotOwners.Represents objects.flagsBlock heap owners →
      CReadOnly.Preserves (pool.install literalBase firstBlock signed) heap →
      MENumericalHistory.Stored heap p clock reference addresses buffer → Reset.Storage heap p →
      ReferenceTrace buffer reference clock actions final finalClock →
      (∀ action ∈ actions, action.Prepared objects heap addresses buffer) →
      (∀ action ∈ actions, config.StoragePolicy action.CallerRegion) →
      Trace model objects owners config program p addresses buffer heap reference clock actions final finalClock := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program config actual reset enterDefined exitDefined heap p clock reference final finalClock addresses buffer actions owners
    valid configured inPool represented literals stored storage admitted ready policies
  induction admitted generalizing heap with
  | nil => exact .nil stored storage configured represented
  | cons accepted _ ih =>
    obtain ⟨returns, blocked, called, returned⟩ := action_correct header objects model sigs pool prepared counts literalBase firstBlock signed
      program config actual reset enterDefined exitDefined heap p _ _ addresses buffer _ owners valid configured
      inPool represented literals stored storage accepted (ready _ (by simp))
    refine .cons called returned ?_
    intro observed after epochs outcome
    have next := returned observed after epochs outcome
    apply ih after next.configuration next.ownership (literals.trans next.readonly) next.stored next.resetStorage
    · intro action member
      exact (ready action (List.mem_cons_of_mem _ member)).preserved action
        (next.storage action.CallerRegion (policies action (List.mem_cons_of_mem _ member)))
    · intro action member
      exact policies action (List.mem_cons_of_mem _ member)

end Rumoca.FMI3.MEMixedRun
end
