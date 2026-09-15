import RumocaFMI3.MEMixedRun
import RumocaFMI3.LoggingCapabilityViews

noncomputable section
namespace Rumoca.FMI3.MEMixedRun
open CTree CMemory CBody StaticFactory CCalls.Events

theorem retained_field_outside (stored : MENumericalHistory.Stored heap p clock reference addresses buffer)
    (name : String) (retained : name ∉ InitializationAccess.writtenFields) :
    MENumericalRun.Outside p addresses buffer (p.member name) := by
  have different (field : String) (member : field ∈ InitializationAccess.writtenFields) :
      p.member name ≠ p.member field := by
    intro same
    exact retained ((Address.member_inj _ _ _).mp same ▸ member)
  have outputs : ∀ label ∈ DiscreteCalls.names, p.member name ≠ addresses label := by
    intro label declared same
    exact stored.control.outside label declared (by simpa using (congrArg Address.block same).symm)
  exact ⟨⟨⟨different "time" (by decide), different "mode" (by decide), different "eventTime" (by decide),
    different "timeMin" (by decide), different "lastCompleted" (by decide), outputs⟩,
    Ne.symm (HistoryBodies.state_ne_field p name), stored.field_ne_buffer name⟩,
    different "stop" (by decide), different "stopDefined" (by decide)⟩

/-- Existing operations retain the flag exactly. The same result structure
also admits a setter's precise replacement of that cell. -/
theorem Returned.of_frame [CInterface] {model : Solve.FMI3Model source} {objects : Objects}
    {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability} {action : Action}
    (configured : capability.Configured heap p enabled)
    (before : MENumericalHistory.Stored heap p clock reference addresses buffer)
    (inPool : p.block = objects.instances.block) (unchanged : action.loggingUpdate = none)
    (stored : MENumericalHistory.Stored after p (action.clock clock) (action.next reference) addresses buffer)
    (reset : Reset.Storage after p) (ownership : SlotOwners.Represents objects.flagsBlock after owners)
    (observation : action.Observed model reference observed) (readonly : CReadOnly.Preserves heap after)
    (frame : ∀ q, MEFailure.Protected objects addresses buffer q → MENumericalRun.Outside p addresses buffer q → after q = heap q)
    (storage : ∀ region, capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after → CStorage.PreservesOn region before after) →
      CStorage.PreservesOn region heap after)
    (callerFrame : ∀ region : Address → Prop, capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after → ∀ q, region q → after q = before q) →
      ∀ q, region q → MENumericalRun.Outside p addresses buffer q → ¬ action.CallerRegion q → after q = heap q) :
    Returned model objects owners capability enabled p addresses buffer heap after reference clock action observed := by
  have keeps : InitializationProtocol.Retention none p heap after := .of_retains
    (fun name outside => frame (p.member name) (Or.inl inPool) (retained_field_outside before name outside))
  refine ⟨stored, reset, ?_, ?_, ownership, observation, readonly,
    (fun q guarded outside _ => frame q guarded outside), storage,
    fun region policy q inside outside _ disjoint => callerFrame region policy q inside outside disjoint⟩
  · simpa only [unchanged] using keeps.configured configured
  · simpa only [unchanged] using keeps

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
    (nominals : NominalEnvironment.PreparedContract model sigs pool)
    (logging : DebugLogging.PreparedContract model sigs pool)
    (eventIndicators : EventIndicatorEnvironment.PreparedContract model sigs pool)
    (literalBase : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation) (capability : Logging.Capability) (enabled : Bool),
      program.internal = LiteralPreparation.program model sigs →
      program.externals "strcmp" = some (CStringCalls.compareExternal (by rfl)) →
      capability.Bound program →
      StaticReset.ExecutionContract program →
      program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
      program.internal.definitions InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) →
      ∀ heap p clock reference addresses buffer action (owners : SlotOwners.State objects.capacity),
      capability.Requires (fun _ effect => MEFailure.Respects effect objects addresses buffer) →
      capability.Configured heap p enabled → Reset.Writable heap (p.member "logging") .boolean →
      p.block = objects.instances.block → SlotOwners.Represents objects.flagsBlock heap owners →
      CReadOnly.Preserves (pool.install literalBase firstBlock signed) heap →
      MENumericalHistory.Stored heap p clock reference addresses buffer → Reset.Storage heap p →
      action.Allowed buffer clock reference →
      action.Prepared objects heap addresses buffer →
      ∃ returns blocked, ActionContract program p addresses buffer heap action returns blocked ∧
        ∀ observed after epochs, returns observed after epochs →
          Returned model objects owners capability enabled p addresses buffer heap after reference clock action observed := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program capability enabled actual compare bound reset enterDefined exitDefined heap p clock reference addresses buffer action owners
    required configured writable inPool represented literals stored storage allowed ready
  let config := capability.meView enabled
  have valid : config.Valid program objects addresses buffer := capability.me_valid bound required enabled
  have current : config.Stored heap p := capability.me_stored configured
  have storagePolicy (region : Address → Prop) (policy : capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after → CStorage.PreservesOn region before after)) :
      config.StoragePolicy region := capability.me_storage policy enabled
  have framePolicy (region : Address → Prop) (policy : capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after → ∀ q, region q → after q = before q)) :
      config.FramePolicy region := capability.me_frame policy enabled
  cases action with
  | counts request =>
    obtain ⟨outcomes, blocked, contract⟩ := MECountCalls.execution header objects model sigs pool counts
      literalBase firstBlock signed program config actual heap p clock reference addresses buffer request owners
      valid current inPool represented literals stored storage ready.1 ready.2 allowed
    refine ⟨_, blocked, .counts contract, ?_⟩
    rintro observed after epochs ⟨events, status, rfl, rfl, returned⟩
    obtain ⟨observation, memory⟩ := contract.returned events status after returned
    refine Returned.of_frame configured stored inPool rfl memory.stored memory.reset memory.ownership ?_ memory.readonly
      (fun q guarded outside => memory.frame q guarded outside.1.1.2.1)
      (fun region policy => memory.storage region (storagePolicy region policy)) ?_
    · cases request with
      | get which output =>
        obtain ⟨statusEq, quiet, readback⟩ := observation
        have empty := quiet rfl
        simp only [Action.Observed, statusEq, empty, readback, CountAccess.Request.failed,
          Bool.false_eq_true, ↓reduceIte, MENumericalHistory.Observation.ok]
      | reject which missing output =>
        exact ⟨events, by simp only [CountAccess.Request.readback, observation.1,
          CountAccess.Request.failed, ↓reduceIte]⟩
    · intro region policy q inside outside disjoint
      apply memory.callerFrame region (framePolicy region policy) q inside outside.1.1.2.1
      cases request <;> first | exact disjoint | trivial
  | nominals request =>
    obtain ⟨outcomes, blocked, contract⟩ := MENominalCalls.execution header objects model sigs pool nominals
      literalBase firstBlock signed program config actual heap p clock reference addresses buffer request owners
      valid current inPool represented literals stored storage ready.1 ready.2 allowed
    refine ⟨_, blocked, .nominals contract, ?_⟩
    rintro observed after epochs ⟨events, status, rfl, rfl, returned⟩
    obtain ⟨observation, memory⟩ := contract.returned events status after returned
    refine Returned.of_frame configured stored inPool rfl memory.stored memory.reset memory.ownership ?_ memory.readonly
      (fun q guarded outside => memory.frame q guarded outside)
      (fun region policy => memory.storage region (storagePolicy region policy)) ?_
    · cases request with
      | get output =>
        obtain ⟨statusEq, quiet, readback⟩ := observation
        have empty := quiet rfl
        have readbackAt := congrFun readback 0
        simp only [Action.Observed, statusEq, empty, readbackAt, NominalAccess.Request.failed,
          Bool.false_eq_true, ↓reduceIte, MENumericalHistory.Observation.ok]
      | reject access output count =>
        exact ⟨events, by simp only [NominalAccess.Request.readback, observation.1,
          NominalAccess.Request.failed, ↓reduceIte]⟩
    · intro region policy q inside outside disjoint
      apply memory.callerFrame region (framePolicy region policy) q inside outside.1.1.2.1
      cases request <;> first | exact disjoint | trivial
  | run command =>
    obtain ⟨after, epochs, called, nextStored, nextReset, readonly, atomic, keptStorage, frame⟩ :=
      run_correct header objects (pool.addresses firstBlock) model program
        (prepared.quiet header Invocation objects firstBlock program actual) reset enterDefined exitDefined
        heap p clock reference addresses buffer command stored storage allowed
    refine ⟨_, False, .run called, ?_⟩
    rintro observed next checkpoints ⟨rfl, rfl, rfl⟩
    exact Returned.of_frame configured stored inPool rfl nextStored nextReset
      (SlotOwners.ordinary_preserves represented atomic) rfl readonly (fun q _ outside => frame q outside)
      (fun region _ => keptStorage.on region) (fun _ _ q _ outside _ => frame q outside)
  | reject request input =>
    obtain ⟨preparation, readyStored, readyReset, readyReadonly, readyAtomic⟩ := MEFailure.prepare_correct input stored storage
    let ready := MEFailure.prepare input heap buffer
    have readyStorage := preparation.storage
    have condition := MEFailure.Request.Selected.condition allowed readyStored
    obtain ⟨category, message, _, _, _, _, silent, logged⟩ :=
      request.prepared prepared header literalBase firstBlock signed objects ready (literals.trans readyReadonly)
    have readyOwners := SlotOwners.ordinary_preserves represented readyAtomic
    have readyConfig : config.Stored ready p := by
      apply current.framed
      intro name _
      exact MEFailure.prepare_frame input heap buffer _ (stored.field_ne_buffer name)
    have finishFrame (after : Heap)
        (frame : ∀ q, MEFailure.Protected objects addresses buffer q → q ≠ p.member "mode" → after q = ready q) :
        ∀ q, MEFailure.Protected objects addresses buffer q → MENumericalRun.Outside p addresses buffer q → after q = heap q := by
      intro q guarded outside
      exact (frame q guarded outside.1.1.2.1).trans (MEFailure.prepare_frame input heap buffer q outside.1.2.2)
    cases view : config with
    | quiet logger logging =>
      simp only [view, Configuration.Valid, Configuration.Stored,
        Configuration.StoragePolicy, Configuration.FramePolicy] at valid readyConfig storagePolicy framePolicy
      have called := silent Invocation program actual p .me reference.control.mode logger logging
        readyStored.control.kind readyStored.control.mode condition readyConfig.1 readyConfig.2 valid
      have frame := finishFrame _ (fun q _ other => LifecycleBodies.write_frame ready p q .terminated other)
      refine ⟨_, False, .quiet preparation called, ?_⟩
      rintro observed after epochs ⟨rfl, rfl, rfl⟩
      exact Returned.of_frame configured stored inPool rfl readyStored.failed (readyStored.failed_reset readyReset)
        (SlotOwners.ordinary_preserves readyOwners readyStored.failed_atomic) ⟨[], rfl⟩
        (readyReadonly.trans (termination_preserves ((called _).mpr rfl))) frame
        (fun region _ => (readyStorage.trans (CStorage.replace_typed readyStored.control.mode
          ⟨.int32, true, some (.integer Mode.terminated.code)⟩ rfl rfl)).on region)
        (fun _ _ q _ outside _ => (LifecycleBodies.write_frame ready p q .terminated outside.1.1.2.1).trans
          (MEFailure.prepare_frame input heap buffer q outside.1.2.2))
    | logged logger environment name effect =>
      simp only [view, Configuration.Valid, Configuration.Stored,
        Configuration.StoragePolicy, Configuration.FramePolicy] at valid readyConfig storagePolicy framePolicy
      obtain ⟨address, external, policy⟩ := valid
      have called := (logged program actual p logger environment .me reference.control.mode name effect address external
        readyStored.control.kind readyStored.control.mode condition readyConfig.1 readyConfig.2.1 readyConfig.2.2).1
      refine ⟨_, _, .logged name effect (Logging.arguments environment category message) preparation called, ?_⟩
      rintro observed after epochs ⟨rfl, rfl, value, outcome⟩
      obtain ⟨nextStored, nextReset, nextOwners, preserved⟩ := policy.returned readyStored readyReset inPool readyOwners outcome
      have frame := finishFrame after preserved
      exact Returned.of_frame configured stored inPool rfl nextStored nextReset nextOwners ⟨_, rfl⟩
        (readyReadonly.trans (termination_preserves ((called _).mpr (Or.inl ⟨value, after, outcome, rfl⟩)))) frame
        (fun region preserve =>
          ((readyStorage.trans (CStorage.replace_typed readyStored.control.mode
            ⟨.int32, true, some (.integer Mode.terminated.code)⟩ rfl rfl)).on region).trans
            (storagePolicy region preserve _ _ _ _ outcome))
        (fun region preserve q inside outside _ => (framePolicy region preserve _ _ _ _ outcome q inside).trans
          ((LifecycleBodies.write_frame ready p q .terminated outside.1.1.2.1).trans
            (MEFailure.prepare_frame input heap buffer q outside.1.2.2)))
  | eventIndicators request =>
    obtain ⟨outcomes, blocked, contract⟩ := MEEventIndicatorCalls.execution header objects model sigs pool eventIndicators
      literalBase firstBlock signed program config actual heap p clock reference addresses buffer request owners
      valid current inPool represented literals stored storage allowed
    refine ⟨_, blocked, .eventIndicators contract, ?_⟩
    rintro observed after epochs ⟨events, status, rfl, rfl, returned⟩
    obtain ⟨observation, memory⟩ := contract.returned events status after returned
    refine Returned.of_frame configured stored inPool rfl memory.stored memory.reset memory.ownership ?_ memory.readonly
      memory.frame (fun region policy => memory.storage region (storagePolicy region policy)) ?_
    · obtain ⟨statusValue, quiet⟩ := observation
      cases failed : request.failed with
      | false =>
        have empty := quiet failed
        simp only [Action.Observed, failed, Bool.false_eq_true, if_false, statusValue,
          empty, MENumericalHistory.Observation.ok]
      | true =>
        simp only [Action.Observed, failed, if_true]
        exact ⟨events, by simp only [statusValue, failed, if_true]⟩
    · intro region policy q inside outside _
      exact memory.callerFrame region (framePolicy region policy) q inside outside.1.1.2.1
  | logging request =>
    obtain ⟨outcomes, blocked, contract⟩ := MELoggingCalls.execution header objects model sigs pool logging
      literalBase firstBlock signed program capability enabled actual compare bound heap p clock reference addresses buffer request owners
      configured required inPool represented literals stored storage ready writable
    refine ⟨_, blocked, .logging contract, ?_⟩
    rintro observed after epochs ⟨events, status, rfl, rfl, returned⟩
    obtain ⟨observation, memory⟩ := contract.returned events status after returned
    refine ⟨memory.stored, memory.reset, ?_, memory.retention inPool, memory.ownership, ?_, memory.readonly,
      (fun q guarded outside different => memory.frame q guarded outside.1.1.2.1 different), memory.storage,
      fun region policy q inside outside different _ => memory.callerFrame region policy q inside outside.1.1.2.1 different⟩
    · simpa only [Action.loggingUpdate, DebugLogging.Request.logging_update] using memory.configuration
    · obtain ⟨statusValue, quiet⟩ := observation
      by_cases failed : request.failed = true
      · simp only [Action.Observed, failed, if_true]
        exact ⟨events, by simp only [statusValue, failed, if_true]⟩
      · have passed : request.failed = false := Bool.eq_false_iff.mpr failed
        have empty := quiet passed
        simp only [Action.Observed, passed, Bool.false_eq_true, if_false, statusValue,
          empty, MENumericalHistory.Observation.ok]

end Rumoca.FMI3.MEMixedRun
end


noncomputable section
namespace Rumoca.FMI3.MEMixedRun
open CTree CMemory CBody StaticFactory CCalls.Events

/-- Original caller storage and borrowed input contents are transported
through each actual return. The separation and callback policies apply to the
whole borrowed region; they neither supply future heaps nor require returns. -/
theorem trace_correct (header : CFenv.Header) (objects : Objects) (model : Solve.FMI3Model source)
    (sigs : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap CLiteral.functionNames))
    (prepared : MEEnvironment.PreparedContract model sigs pool)
    (counts : ∀ events, CountEnvironment.PreparedContract model sigs events pool)
    (nominals : NominalEnvironment.PreparedContract model sigs pool)
    (logging : DebugLogging.PreparedContract model sigs pool)
    (eventIndicators : EventIndicatorEnvironment.PreparedContract model sigs pool)
    (literalBase : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation) (capability : Logging.Capability) (enabled : Bool),
      program.internal = LiteralPreparation.program model sigs →
      program.externals "strcmp" = some (CStringCalls.compareExternal (by rfl)) →
      capability.Bound program → StaticReset.ExecutionContract program →
      program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
      program.internal.definitions InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) →
    ∀ (heap : Heap) (p : Address) (clock : Time.Clock) (reference final : MENumericalHistory.ReferenceState)
      (finalClock : Time.Clock) (addresses : String → Address) (buffer : Address) (actions : List Action)
      (owners : SlotOwners.State objects.capacity),
      capability.Requires (fun _ effect => MEFailure.Respects effect objects addresses buffer) →
      capability.Configured heap p enabled → Reset.Writable heap (p.member "logging") .boolean →
      p.block = objects.instances.block → SlotOwners.Represents objects.flagsBlock heap owners →
      CReadOnly.Preserves (pool.install literalBase firstBlock signed) heap →
      MENumericalHistory.Stored heap p clock reference addresses buffer → Reset.Storage heap p →
      ReferenceTrace buffer reference clock actions final finalClock →
      (∀ action ∈ actions, action.Prepared objects heap addresses buffer) →
      (∀ action ∈ actions, capability.Requires (fun _ effect =>
        ∀ args before value after, effect.execute args before value after →
          CStorage.PreservesOn action.CallerRegion before after)) →
      (∀ action ∈ actions, capability.Requires (fun _ effect =>
        ∀ args before value after, effect.execute args before value after →
          ∀ q, action.ReaderRegion q → after q = before q)) →
      (∀ action ∈ actions, ∀ q, action.ReaderRegion q →
        MENumericalRun.Outside p addresses buffer q ∧ q ≠ p.member "logging") →
      (∀ writer ∈ actions, ∀ reader ∈ actions, ∀ q, reader.ReaderRegion q → ¬ writer.CallerRegion q) →
      Trace model objects owners capability program p addresses buffer heap enabled reference clock actions final finalClock := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program capability enabled actual compare bound reset enterDefined exitDefined heap p clock reference final finalClock
    addresses buffer actions owners required configured writable inPool represented literals stored storage admitted ready
    policies readPolicies readerOutside separate
  induction admitted generalizing heap enabled with
  | nil => exact .nil stored storage configured represented
  | @cons rest final finalClock before clock action accepted _ ih =>
    obtain ⟨returns, blocked, called, returned⟩ := action_correct header objects model sigs pool prepared counts nominals logging eventIndicators
      literalBase firstBlock signed program capability enabled actual compare bound reset enterDefined exitDefined
      heap p clock before addresses buffer action owners required configured writable inPool represented literals stored storage
      accepted (ready _ (by simp))
    refine .cons called returned ?_
    intro observed after epochs outcome
    have next := returned observed after epochs outcome
    apply ih (action.loggingUpdate.getD enabled) after next.configuration (next.retention.writable writable)
      next.ownership (literals.trans next.readonly) next.stored next.resetStorage
    · intro reader member
      have original := ready reader (List.mem_cons_of_mem _ member)
      apply original.preserved reader
      · exact next.storage reader.CallerRegion (policies reader (List.mem_cons_of_mem _ member))
      · intro q inside
        have outside := readerOutside reader (List.mem_cons_of_mem _ member) q inside
        exact next.callerFrame reader.ReaderRegion (readPolicies reader (List.mem_cons_of_mem _ member))
          q inside outside.1 outside.2 (separate action (by simp) reader (List.mem_cons_of_mem _ member) q inside)
    · intro reader member
      exact policies reader (List.mem_cons_of_mem _ member)
    · intro reader member
      exact readPolicies reader (List.mem_cons_of_mem _ member)
    · intro reader member
      exact readerOutside reader (List.mem_cons_of_mem _ member)
    · intro writer written reader read
      exact separate writer (List.mem_cons_of_mem _ written) reader (List.mem_cons_of_mem _ read)

end Rumoca.FMI3.MEMixedRun
end
