import RumocaFMI3.CSRunExecution
import RumocaFMI3.CSRunRecordSemantics

noncomputable section
namespace Rumoca.FMI3.CSRun
open CTree CMemory CBody StaticFactory CCalls

/-- Two complete silent-call contracts for the same invocation must describe
one returned heap. This lemma does not impose determinism on foreign callbacks. -/
theorem Executed.heap_unique {E : Type} [CInterface] {program : Events.Program E}
    (first : Executed program p heap action after status) (second : Executed program p heap action other status) :
    after = other := by
  cases first with
  | step called =>
    cases second with
    | step other => simpa using (other _).mp ((called _).mpr rfl)
  | restart reset enter leave => cases second; rfl

/-- Every actual mixed action preserves cells outside its instance and
caller outputs. The execution premise is supplied by change_correct in the
composed trace theorem; it is not a host-supplied successful-run assumption. -/
theorem executed_frame (header : CFenv.Header) (objects : Objects)
    (model : Solve.FMI3Model source) (signatures : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model signatures).flatMap CLiteral.functionNames))
    (prepared : StepCalls.PreparedContract model signatures pool)
    (literalBase : Heap) (firstBlock : Nat) (signed : Bool) (p : Address) (buffers : StepEntry.Buffers) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Events.Program E) (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
    program.internal = LiteralPreparation.program model signatures →
    program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
    program.externals "floor" = some (CMathCalls.floorExternal rfl) →
    ∀ (heap after : Heap) (before next : Reference) (action : Action) (status : Int),
    CReadOnly.Preserves (pool.install literalBase firstBlock signed) heap →
    Stored model.solve heap p buffers before → Suppressed heap p →
    Change header p buffers before action next status → Executed program p heap action after status →
    ∀ query, Outside p buffers query → after query = heap query := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program range actual rounding floorBound heap after before next action status literalFrame stored quiet changed executed query outside
  cases changed with
  | accepted mode accepted =>
    obtain ⟨called, _, _⟩ := CSHistory.step header objects (pool.addresses firstBlock) model signatures
      before.seed p buffers before.current _ before.stop _
      (prepared.quiet _ objects firstBlock).2 program heap range actual rounding floorBound (stored.step_mode mode) accepted
    rw [executed.heap_unique (.step called)]
    exact CSHistory.written_frame model.solve before.seed heap p buffers before.current _ query outside.cs
  | rejected reason selection selected =>
    rename_i request outputs
    obtain ⟨_, _, _, _, _, _, rejected, _⟩ := prepared.rejections _ literalBase firstBlock signed objects heap literalFrame
    obtain ⟨logger, logging, loggerValue, loggingValue, suppressed⟩ := quiet
    have reads := stored.rejection_reads header request outputs header.nearest reason selection selected
    have called := rejected E program reason p request.flag range logger logging actual (fun _ => rounding)
      (fun _ _ => floorBound) rfl reads selected (fun _ => stored.reset.mode) loggerValue loggingValue suppressed
    rw [executed.heap_unique (.step called)]
    exact rejection_frame reason _ heap p buffers selection selected query outside
  | restart _ =>
    cases executed
    exact StaticReset.restarted_frame heap p query _ .cs outside.1

/-- Derive all calls, persistent storage and the ordinary memory frame
from the initial heap and independent reference history. -/
theorem trace_framed (header : CFenv.Header) (objects : Objects)
    (model : Solve.FMI3Model source) (signatures : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model signatures).flatMap CLiteral.functionNames))
    (prepared : StepCalls.PreparedContract model signatures pool)
    (literalBase : Heap) (firstBlock : Nat) (signed : Bool) (p : Address) (buffers : StepEntry.Buffers) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Events.Program E)
      (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
    program.internal = LiteralPreparation.program model signatures →
    program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
    program.externals "floor" = some (CMathCalls.floorExternal rfl) →
    StaticReset.ExecutionContract program →
    program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
    program.internal.definitions InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) →
    ∀ (heap : Heap) (before final : Reference) (actions : List Action) (statuses : List Int),
    CReadOnly.Preserves (pool.install literalBase firstBlock signed) heap →
    Stored model.solve heap p buffers before → Suppressed heap p →
    ReferenceTrace header p buffers before actions final statuses →
    ∃ after, Calls model.solve program p buffers heap before actions after final statuses ∧
      Stored model.solve after p buffers final ∧ Retains p heap after ∧ CReadOnly.Preserves heap after ∧
      CAtomicBoolean.Preserves heap after ∧
      (∀ query, Outside p buffers query → after query = heap query) ∧
      (∀ observed events actualAfter records, Recorded program p heap actions observed events actualAfter records →
        SemanticTrace model.solve header p buffers heap before actions observed records actualAfter final) := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program range actual rounding floorBound reset enterDefined exitDefined heap before final actions statuses
    literals stored quiet trace
  induction trace generalizing heap with
  | nil =>
    refine ⟨heap, .nil, stored, fun _ _ => rfl, .refl _, .refl _, fun _ _ => rfl, ?_⟩
    intro observed events actualAfter records actual
    cases actual
    exact .nil
  | cons changed _ ih =>
    obtain ⟨next, called, nextStored, observed, retained, atomic, storage, frame⟩ := change_correct header objects model signatures pool prepared literalBase firstBlock
      signed p buffers program range actual rounding floorBound reset enterDefined exitDefined heap _ _ _ _ literals stored quiet changed
    obtain ⟨after, calls, finalStored, retainedAfter, readonly, atomicAfter, laterFrame, laterRecords⟩ := ih next (literals.trans called.readonly)
      nextStored (retained.suppressed quiet)
    refine ⟨after, .cons called nextStored observed ⟨storage, atomic, retained, frame⟩ calls, finalStored, retained.trans retainedAfter,
      called.readonly.trans readonly, atomic.trans atomicAfter,
      (fun query outside => (laterFrame query outside).trans (frame query outside)), ?_⟩
    intro observedStatuses events actualAfter records actual
    cases actual with
    | cons head tail =>
      obtain ⟨_, _, sameHeap, headSemantic⟩ := called.recorded_correct changed nextStored observed head
      cases sameHeap
      exact .cons headSemantic (laterRecords _ _ _ _ tail)

end Rumoca.FMI3.CSRun
end
