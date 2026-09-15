import RumocaFMI3.CSRunLogging
import RumocaFMI3.CSRunStatus

noncomputable section
namespace Rumoca.FMI3.CSRun
open CTree CMemory CBody StaticFactory CCalls

/-- Each actual action supplies all its returning alternatives and the
explicit no-return alternative. The callback frame holds universally over the
external relation; there is no assumed successful callback or later heap. -/
theorem change_logged_correct (header : CFenv.Header) (objects : Objects)
    (model : Solve.FMI3Model source) (signatures : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model signatures).flatMap CLiteral.functionNames))
    (prepared : StepCalls.PreparedContract model signatures pool)
    (literalBase : Heap) (firstBlock : Nat) (signed : Bool) (p : Address) (buffers : StepEntry.Buffers)
    (inPool : p.block = objects.instances.block) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Events.Program Events.Invocation)
      (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31) (logger : Logger),
    program.internal = LiteralPreparation.program model signatures →
    program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
    program.externals "floor" = some (CMathCalls.floorExternal rfl) →
    logger.Bound program → logger.Respects objects buffers →
    StaticReset.ExecutionContract program →
    program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
    program.internal.definitions InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) →
    ∀ (heap : Heap) (before next : Reference) (action : Action) (status : Int)
      (owners : SlotOwners.State objects.capacity),
    CReadOnly.Preserves (pool.install literalBase firstBlock signed) heap →
    Stored model.solve heap p buffers before → logger.Stored heap p →
    SlotOwners.Represents objects.flagsBlock heap owners →
    Change header p buffers before action next status →
    ∃ returns blocked, ActionContract program p heap action status returns blocked ∧
      ∀ events after, returns events after →
        Returned objects logger owners model.solve p buffers heap after next action status := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program range logger actual rounding floorBound bound policy reset enterDefined exitDefined
    heap before next action status owners literals stored logging represented changed
  cases changed with
  | accepted mode accepted =>
    rename_i request advanced
    obtain ⟨called, _, outputs⟩ := CSHistory.step header objects (pool.addresses firstBlock) model signatures
      before.seed p buffers before.current _ before.stop _
      (prepared.quiet _ objects firstBlock).2 program heap range actual rounding floorBound (stored.step_mode mode) accepted
    have retained := advance_retains stored advanced
    refine ⟨_, False, .silent (.step called), ?_⟩
    rintro events after ⟨rfl, rfl⟩
    exact ⟨stored.advance mode _, retained.logger logging,
      SlotOwners.ordinary_preserves represented (advance_atomic stored mode _), fun _ => outputs,
      retained, Events.termination_preserves ((called _).mpr rfl),
      (fun query _ outside => CSHistory.written_frame model.solve before.seed heap p buffers before.current _ query outside.cs),
      (fun region _ => (advance_storage stored advanced).on region),
      fun _ _ query _ outside => CSHistory.written_frame model.solve before.seed heap p buffers before.current _ query outside.cs⟩
  | rejected reason selection selected =>
    rename_i request outputs
    obtain ⟨category, messages, _, _, _, _, _, logged⟩ := prepared.rejections _ literalBase firstBlock signed objects heap literals
    have reads := stored.rejection_reads header request outputs header.nearest reason selection selected
    obtain ⟨called, _⟩ := logged program reason p logger.pointer request.flag range logger.environment logger.name logger.effect
      actual (fun _ => rounding) (fun _ _ => floorBound) bound.1 bound.2 rfl reads selected
      (fun _ => stored.reset.mode) logging.1 logging.2.1 logging.2.2
    have preStored := stored.reject header request outputs header.nearest reason selection selected
    have preRetained := reject_retains stored header request outputs header.nearest reason selection selected
    have preOwners := SlotOwners.ordinary_preserves represented (StepRejections.after_atomic reason _ heap p reads selected stored.reset)
    refine ⟨_, _, .logged logger.name logger.effect
      (StepRejections.arguments reason logger.environment category (messages reason)) called, ?_⟩
    rintro events after ⟨rfl, value, performed⟩
    have kept := policy _ _ _ _ performed
    have controls := preRetained.trans (kept.retains inPool)
    exact ⟨preStored.framed (kept.run inPool), controls.logger logging, kept.owners preOwners,
      (by intro zero; cases reason <;> simp [StepRejections.status] at zero), controls,
      Events.termination_preserves ((called _).mpr (Or.inl ⟨value, after, performed, rfl⟩)),
      (fun query isProtected outside => (kept query isProtected).trans
        (rejection_frame reason _ heap p buffers selection selected query outside)),
      (fun region preserve => ((StepRejections.after_storage reason _ heap p reads selected stored.reset).on region).trans
        (preserve _ _ _ _ performed)),
      fun _ preserve query inside outside => (preserve _ _ _ _ performed query inside).trans
        (rejection_frame reason _ heap p buffers selection selected query outside)⟩
  | restart admissible =>
    rename_i args
    obtain ⟨entered, exited⟩ := InitializationEnvironment.calls header objects (pool.addresses firstBlock) model
      program (Reset.finalHeap heap p) p _ .cs enterDefined exitDefined admissible
      (StaticReset.entry_storage heap p) ((StaticReset.kind_value heap p).trans stored.kind)
    have executed : Executed program p heap (.restart args)
        (InitializationCalls.exitedHeap (Reset.finalHeap heap p) p args .cs) 0 :=
      .restart (reset.successful heap p .cs before.mode stored.reset stored.kind stored.mode) entered exited
    have retained := restart_retains heap p args
    refine ⟨_, False, .silent executed, ?_⟩
    rintro events after ⟨rfl, rfl⟩
    exact ⟨stored.restart _ admissible, retained.logger logging,
      SlotOwners.ordinary_preserves represented (restart_atomic stored.reset _), True.intro,
      retained, executed.readonly, (fun query _ outside => StaticReset.restarted_frame heap p query _ .cs outside.1),
      (fun region _ => (InitializationStorage.restarted model heap p .cs before.mode stored.reset
        stored.kind stored.mode args admissible).on region),
      fun _ _ query _ outside => StaticReset.restarted_frame heap p query args .cs outside.1⟩

theorem ActionContract.recorded_correct [CInterface] {program : Events.Program Events.Invocation}
    {before next : Reference}
    (certified : ActionContract program p heap action status returns blocked)
    (changed : Change header p buffers before action next status)
    (returned : ∀ events after, returns events after →
      Stored model after p buffers next ∧ Observation buffers next action status after)
    (actual : RecordedAction program p heap action observed events after records) :
    SemanticAction model header p buffers heap before action observed records after next := by
  cases actual with
  | step performed =>
    obtain ⟨same, outcome⟩ := certified.performed_status performed
    have post := returned _ _ outcome
    exact .step (record := (⟨observed, events, after⟩ : CallRecord Events.Invocation))
      (by simpa only [same] using changed) post.1 (by simpa only [same] using post.2)
  | restart resetCall enterCall exitCall =>
    cases certified with
    | silent executed =>
      have post := returned [] _ ⟨rfl, rfl⟩
      exact (executed.recorded_correct changed post.1 post.2 (.restart resetCall enterCall exitCall)).2.2.2

/-- An arbitrary finite mixed reference history has a complete branching call
certificate under the universal logger frame. Every returned callback branch
retains its source/Solve state, public successful outputs, ownership and the
storage needed by subsequent rejection/recovery. No return is assumed. -/
theorem logged_trace_correct (header : CFenv.Header) (objects : Objects)
    (model : Solve.FMI3Model source) (signatures : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model signatures).flatMap CLiteral.functionNames))
    (prepared : StepCalls.PreparedContract model signatures pool)
    (literalBase : Heap) (firstBlock : Nat) (signed : Bool) (p : Address) (buffers : StepEntry.Buffers)
    (inPool : p.block = objects.instances.block) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Events.Program Events.Invocation)
      (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31) (logger : Logger),
    program.internal = LiteralPreparation.program model signatures →
    program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
    program.externals "floor" = some (CMathCalls.floorExternal rfl) →
    logger.Bound program → logger.Respects objects buffers →
    StaticReset.ExecutionContract program →
    program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
    program.internal.definitions InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) →
    ∀ (heap : Heap) (before final : Reference) (actions : List Action) (statuses : List Int)
      (owners : SlotOwners.State objects.capacity),
    CReadOnly.Preserves (pool.install literalBase firstBlock signed) heap →
    Stored model.solve heap p buffers before → logger.Stored heap p →
    SlotOwners.Represents objects.flagsBlock heap owners →
    ReferenceTrace header p buffers before actions final statuses →
    LoggedTrace objects logger owners model.solve program p buffers heap before actions final statuses ∧
    (∀ observed events after records, Recorded program p heap actions observed events after records →
      SemanticTrace model.solve header p buffers heap before actions observed records after final) := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program range logger actual rounding floorBound bound policy reset enterDefined exitDefined
    heap before final actions statuses owners literals stored logging represented trace
  induction trace generalizing heap with
  | nil =>
    refine ⟨.nil stored logging represented, ?_⟩
    intro observed events after records actual
    cases actual
    exact .nil
  | cons changed _ ih =>
    obtain ⟨returns, blocked, certified, returned⟩ := change_logged_correct header objects model signatures pool prepared literalBase firstBlock
      signed p buffers inPool program range logger actual rounding floorBound bound policy reset enterDefined exitDefined
      heap _ _ _ _ owners literals stored logging represented changed
    constructor
    · refine .cons certified returned ?_
      intro events after outcome
      have next := returned events after outcome
      exact (ih after (literals.trans next.readonly) next.stored next.logging next.ownership).1
    · intro observed events after records actual
      cases actual with
      | cons head tail =>
        have outcome := (certified.performed_status head.performed).2
        have next := returned _ _ outcome
        have headSemantic := certified.recorded_correct changed
          (fun events after outcome => ⟨(returned events after outcome).stored, (returned events after outcome).observed⟩) head
        exact .cons headSemantic ((ih _ (literals.trans next.readonly) next.stored next.logging next.ownership).2 _ _ _ _ tail)

end Rumoca.FMI3.CSRun
end
