import RumocaFMI3.CSMixedRun
import RumocaFMI3.CSCreationStorage

noncomputable section
namespace Rumoca.FMI3.CSMixedRun
open CTree CMemory CBody StaticFactory CCalls.Events

theorem configuration_cases [CInterface] {capability : Logging.Capability}
    (configured : capability.Configured heap p enabled) :
    CSRun.Suppressed heap p ∨ ∃ logger : CSRun.Logger,
      capability.csLogger = some logger ∧ logger.Stored heap p := by
  cases capability with
  | absent environment =>
    exact Or.inl ⟨none, enabled, configured.1.1, configured.2, Or.inl rfl⟩
  | present address environment name effect =>
    cases enabled with
    | false => exact Or.inl ⟨some address, false, configured.1.1, configured.2, Or.inr rfl⟩
    | true => exact Or.inr ⟨⟨address, environment, name, effect⟩, rfl,
        ⟨configured.1.1, configured.2, configured.1.2⟩⟩

theorem Returned.quiet [CInterface] {objects : Objects}
    {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}
    (configured : capability.Configured heap p enabled)
    (stored : CSRun.Stored model after p buffers reference)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (observation : CSRun.Observation buffers reference action expected after)
    (retained : CSRun.Retains p heap after) (readonly : CReadOnly.Preserves heap after)
    (atomic : CAtomicBoolean.Preserves heap after) (storage : CStorage.Preserves heap after)
    (frame : ∀ q, CSRun.Outside p buffers q → after q = heap q) :
    Returned objects owners model capability enabled p buffers heap after reference (.run action) expected [] (.integer expected) := by
  have keeps : InitializationProtocol.Retention none p heap after := .of_retains retained
  exact ⟨stored, keeps.configured configured, keeps, SlotOwners.ordinary_preserves ownership atomic,
    ⟨rfl, observation⟩, readonly, (fun q _ outside => frame q outside),
    (fun region _ => storage.on region), fun _ _ q _ outside _ => frame q outside⟩

theorem Returned.logged [CInterface] {objects : Objects}
    {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability} {logger : CSRun.Logger}
    (selected : capability.csLogger = some logger)
    (configured : capability.Configured heap p enabled)
    (post : CSRun.Returned objects logger owners model p buffers heap after reference action expected) :
    Returned objects owners model capability enabled p buffers heap after reference (.run action) expected events (.integer expected) := by
  have keeps : InitializationProtocol.Retention none p heap after := .of_retains post.retained
  exact ⟨post.stored, keeps.configured configured, keeps, post.ownership,
    ⟨rfl, post.observed⟩, post.readonly, post.framed,
    (fun region policy => post.storage region (Logging.Capability.cs_storage selected policy)),
    fun region policy q inside outside _ => post.callerFrame region (Logging.Capability.cs_frame selected policy) q inside outside⟩

theorem Returned.logging [CInterface] {objects : Objects}
    {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability} {request : DebugLogging.Request}
    (configured : capability.Configured heap p enabled)
    (inPool : p.block = objects.instances.block)
    (observation : CSLoggingCalls.CorrectObservation request events status)
    (post : CSLoggingCalls.Memory model objects owners capability enabled heap after p buffers reference request) :
    Returned objects owners model capability enabled p buffers heap after (CSLoggingCalls.next request reference)
      (.logging request) (if request.failed then 3 else 0) events status := by
  have keeps := post.retention inPool
  exact ⟨post.stored, keeps.configured configured, keeps, post.ownership,
    ⟨observation.1, observation⟩, post.readonly,
    (fun q guarded outside => post.frame q guarded (outside.field "mode") (outside.field "logging")),
    post.storage, fun region policy q inside outside _ =>
      post.callerFrame region policy q inside (outside.field "mode") (outside.field "logging")⟩

/-- The accepted query keeps the Solve sample and communication clock. Only
the requested caller arrays and, for termination, the mode cell change. -/
theorem query_correct [CInterface] {program : Program Invocation} {objects : Objects}
    {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}
    {model : Solve.FMI3Model source} (quiet : InstanceQuery.QuietContract model program)
    (request : InstanceQuery.Request)
    (stored : CSRun.Stored model.solve heap p buffers before)
    (configured : capability.Configured heap p enabled)
    (represented : SlotOwners.Represents objects.flagsBlock heap owners)
    (inPool : p.block = objects.instances.block)
    (prepared : (Action.query request).Prepared objects buffers heap)
    (ready : CSRun.CanFinish before.mode) (allowed : request.Allowed .cs before.mode) :
    ∃ after, ActionContract program p heap (.query request)
        (fun events value next => events = [] ∧ value = .integer 0 ∧ next = after) False ∧
      Returned objects owners model.solve capability enabled p buffers heap after (queried request before)
        (.query request) 0 [] (.integer 0) := by
  obtain ⟨storage, separateInstances, unprotected⟩ := prepared
  have separate := separateInstances.rebase inPool
  have instanceStored : Float64Access.Instance heap p .cs before.mode (instanceState model.solve before)
      before.current.time :=
    ⟨by simpa [Kind.code] using stored.kind, stored.mode_cell, stored.state,
      by simp [load, stored.clock, convert, Value.finite]⟩
  obtain ⟨transferred, host, called, instanceAfter, readback, preserved, readonly, atomic, frame⟩ :=
    request.step quiet instanceStored storage separate allowed
  let after := request.after model heap p (instanceState model.solve before) before.current.time
  have record (q : Address) (inside : p.InRecord q) (notState : q ≠ StateProofs.stateAddress p)
      (notMode : q ≠ p.member "mode") : after q = heap q :=
    frame q notState notMode (request.not_record separate inside)
  have field (name : String) (different : name ≠ "mode") : after (p.member name) = heap (p.member name) :=
    record _ (p.member_in_record name) (Ne.symm (HistoryBodies.state_ne_field p name))
      (fun same => different ((Address.member_inj _ _ _).mp same))
  have loaded (name : String) (different : name ≠ "mode") :
      load after (p.member name) = load heap (p.member name) := by
    simp only [load, field name different]
  have sameState : request.nextState (instanceState model.solve before) = instanceState model.solve before :=
    request.cs_state allowed ready
  have nextStored : CSRun.Stored model.solve after p buffers (queried request before) := by
    refine ⟨by simpa [Kind.code] using instanceAfter.kind, ?_, (field "time" (by decide)).trans stored.clock,
      by simpa only [sameState] using instanceAfter.state,
      (loaded "stopDefined" (by decide)).trans stored.stopDefined,
      fun limit chosen => (loaded "stop" (by decide)).trans (stored.stopValue limit chosen),
      stored.reset.preserved preserved, stored.buffers.storage_preserved preserved⟩
    exact instanceAfter.mode_loaded
  have retained : CSRun.Retains p heap after := fun name outside =>
    field name (fun same => outside (by simp [same]))
  have keeps : InitializationProtocol.Retention none p heap after := .of_retains retained
  refine ⟨after, .query host called, ?_⟩
  refine ⟨nextStored, keeps.configured configured, keeps, SlotOwners.ordinary_preserves represented atomic,
    ⟨rfl, rfl, readback⟩, readonly, ?_, fun region _ => preserved.on region, ?_⟩
  · intro q guarded outside
    exact frame q (fun same => outside.1 (same ▸ (p.member_in_record "model").member "x"))
      (outside.field "mode") (fun caller => unprotected q caller guarded)
  · intro region _ q _ outside notCaller
    exact frame q (fun same => outside.1 (same ▸ (p.member_in_record "model").member "x"))
      (outside.field "mode") notCaller

/-- Derive each mixed call from the same emitted table and prepared contracts.
The original callback obligation remains available while the flag is false. -/
theorem action_correct (header : CFenv.Header) (objects : Objects) (model : Solve.FMI3Model source)
    (sigs : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap CLiteral.functionNames))
    (step : StepCalls.PreparedContract model sigs pool)
    (logging : DebugLogging.PreparedContract model sigs pool)
    (literalBase : Heap) (firstBlock : Nat) (signed : Bool) (p : Address) (buffers : StepEntry.Buffers)
    (inPool : p.block = objects.instances.block) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation) (capability : Logging.Capability) (enabled : Bool)
      (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
    program.internal = LiteralPreparation.program model sigs →
    program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
    program.externals "floor" = some (CMathCalls.floorExternal rfl) →
    program.externals "strcmp" = some (CStringCalls.compareExternal rfl) →
    capability.Bound program → capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after → CSRun.ProtectedFrame objects buffers before after) →
    StaticReset.ExecutionContract program → InstanceQuery.QuietContract model program →
    program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
    program.internal.definitions InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) →
    ∀ (heap : Heap) (before next : CSRun.Reference) (action : Action) (status : Int)
      (owners : SlotOwners.State objects.capacity),
    CReadOnly.Preserves (pool.install literalBase firstBlock signed) heap →
    CSRun.Stored model.solve heap p buffers before → capability.Configured heap p enabled →
    Reset.Writable heap (p.member "logging") .boolean → SlotOwners.Represents objects.flagsBlock heap owners →
    action.Prepared objects buffers heap → Change header p buffers before action next status →
    ∃ returns blocked, ActionContract program p heap action returns blocked ∧
      ∀ events value after, returns events value after →
        Returned objects owners model.solve capability enabled p buffers heap after next action status events value := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program capability enabled range actual rounding floorBound compare bound required reset quietQuery enterDefined
    exitDefined heap before next action status owners literals stored configured writable represented inputs changed
  cases changed with
  | run changed =>
    rcases configuration_cases configured with quiet | ⟨logger, selected, active⟩
    · obtain ⟨after, called, nextStored, observed, retained, atomic, storage, frame⟩ :=
        CSRun.change_correct header objects model sigs pool step literalBase firstBlock signed p buffers
          program range actual rounding floorBound reset enterDefined exitDefined heap before next _ status
          literals stored quiet changed
      refine ⟨_, False, .run (.silent called), ?_⟩
      rintro events value final ⟨rfl, rfl, rfl⟩
      exact Returned.quiet configured nextStored represented observed retained called.readonly atomic storage frame
    · obtain ⟨returns, blocked, called, returned⟩ := CSRun.change_logged_correct
        header objects model sigs pool step literalBase firstBlock signed p buffers inPool
        program range logger actual rounding floorBound (Logging.Capability.cs_bound selected bound)
        (Logging.Capability.cs_respects selected required) reset enterDefined exitDefined
        heap before next _ status owners literals stored active represented changed
      refine ⟨_, blocked, .run called, ?_⟩
      rintro events value after ⟨rfl, outcome⟩
      exact Returned.logged selected configured (returned events after outcome)
  | logging =>
    obtain ⟨returns, blocked, called⟩ := CSLoggingCalls.execution header objects model sigs pool logging
      literalBase firstBlock signed program capability enabled actual compare bound heap p before buffers _ owners
      configured required inPool represented literals stored inputs writable
    refine ⟨returns, blocked, .logging called, ?_⟩
    intro events value after outcome
    obtain ⟨observation, memory⟩ := called.returned events value after outcome
    exact Returned.logging configured inPool observation memory
  | query ready allowed =>
    obtain ⟨after, called, post⟩ := query_correct quietQuery _ stored configured represented inPool inputs ready allowed
    refine ⟨_, False, called, ?_⟩
    rintro events value final ⟨rfl, rfl, rfl⟩
    exact post

/-- Every reference history has a branching actual-call certificate.
Original borrowed category contents supply all later requests through derived
frames; the theorem does not quantify an externally supplied future heap. -/
theorem trace_correct (header : CFenv.Header) (objects : Objects) (model : Solve.FMI3Model source)
    (sigs : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap CLiteral.functionNames))
    (step : StepCalls.PreparedContract model sigs pool)
    (logging : DebugLogging.PreparedContract model sigs pool)
    (literalBase : Heap) (firstBlock : Nat) (signed : Bool) (p : Address) (buffers : StepEntry.Buffers)
    (inPool : p.block = objects.instances.block) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation) (capability : Logging.Capability) (enabled : Bool)
      (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
    program.internal = LiteralPreparation.program model sigs →
    program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
    program.externals "floor" = some (CMathCalls.floorExternal rfl) →
    program.externals "strcmp" = some (CStringCalls.compareExternal rfl) →
    capability.Bound program → capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after → CSRun.ProtectedFrame objects buffers before after) →
    StaticReset.ExecutionContract program → InstanceQuery.QuietContract model program →
    program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
    program.internal.definitions InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) →
    ∀ (heap : Heap) (before final : CSRun.Reference) (actions : List Action) (statuses : List Int)
      (owners : SlotOwners.State objects.capacity),
    CReadOnly.Preserves (pool.install literalBase firstBlock signed) heap →
    CSRun.Stored model.solve heap p buffers before → capability.Configured heap p enabled →
    Reset.Writable heap (p.member "logging") .boolean → SlotOwners.Represents objects.flagsBlock heap owners →
    ReferenceTrace header p buffers before actions final statuses →
    (∀ action ∈ actions, action.Prepared objects buffers heap) →
    (∀ action ∈ actions, capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after →
        CStorage.PreservesOn action.CallerRegion before after)) →
    (∀ action ∈ actions, capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after →
        ∀ q, action.ReaderRegion q → after q = before q)) →
    (∀ action ∈ actions, ∀ q, action.ReaderRegion q → CSRun.Outside p buffers q) →
    (∀ writer ∈ actions, ∀ reader ∈ actions, ∀ q, reader.ReaderRegion q → ¬ writer.CallerRegion q) →
    Trace header objects owners model.solve capability program p buffers heap enabled before actions final statuses := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program capability enabled range actual rounding floorBound compare bound required reset quietQuery enterDefined
    exitDefined heap before final actions statuses owners literals stored configured writable represented admitted inputs
    storagePolicies policies guarded separate
  induction admitted generalizing heap enabled with
  | nil => exact .nil stored configured represented
  | @cons action status rest statuses before next final changed following ih =>
    obtain ⟨returns, blocked, called, returned⟩ := action_correct header objects model sigs pool step logging
      literalBase firstBlock signed p buffers inPool program capability enabled range actual rounding floorBound compare
      bound required reset quietQuery enterDefined exitDefined heap before next action status owners literals stored configured
      writable represented (inputs action (by simp)) changed
    refine .cons changed called returned ?_
    intro events value after outcome
    have post := returned events value after outcome
    apply ih (action.loggingUpdate.getD enabled) after (literals.trans post.readonly) post.stored post.configuration
      (post.retention.writable writable) post.ownership
    · intro later member
      exact Action.Prepared.preserved later (inputs later (List.mem_cons_of_mem _ member))
        (post.storage later.CallerRegion (storagePolicies later (List.mem_cons_of_mem _ member)))
        (fun q inside => post.callerFrame later.ReaderRegion (policies later (List.mem_cons_of_mem _ member)) q inside
          (guarded later (List.mem_cons_of_mem _ member) q inside)
          (separate action (by simp) later (List.mem_cons_of_mem _ member) q inside))
    · exact fun later member => storagePolicies later (List.mem_cons_of_mem _ member)
    · exact fun later member => policies later (List.mem_cons_of_mem _ member)
    · exact fun later member => guarded later (List.mem_cons_of_mem _ member)
    · exact fun writer written reader read => separate writer (List.mem_cons_of_mem _ written) reader
        (List.mem_cons_of_mem _ read)

end Rumoca.FMI3.CSMixedRun
end
