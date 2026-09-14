import RumocaFMI3.CSRunTransition
import RumocaFMI3.CSSimulationStorage
import RumocaFMI3.InitializationEnvironment

noncomputable section
namespace Rumoca.FMI3.CSRun
open CTree CMemory CBody StaticFactory CCalls

/-- One reference action executes the prepared public functions and preserves
the persistent run invariant. Logging is suppressed by original configuration;
callback-enabled traces use the separate callback frame obligation. -/
theorem change_correct (header : CFenv.Header) (objects : Objects)
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
    ∀ (heap : Heap) (before after : Reference) (action : Action) (status : Int),
    CReadOnly.Preserves (pool.install literalBase firstBlock signed) heap →
    Stored model.solve heap p buffers before → Suppressed heap p → Change header p buffers before action after status →
    ∃ next, Executed program p heap action next status ∧ Stored model.solve next p buffers after ∧
      Observation buffers after action status next ∧ Retains p heap next ∧ CAtomicBoolean.Preserves heap next ∧
      CStorage.Preserves heap next := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program range actual rounding floorBound reset enterDefined exitDefined heap before after action status
    literals stored suppressed changed
  cases changed with
  | accepted mode accepted =>
    obtain ⟨called, _, outputs⟩ := CSHistory.step header objects (pool.addresses firstBlock) model signatures
      before.seed p buffers before.current _ before.stop _
      (prepared.quiet _ objects firstBlock).2 program heap range actual rounding floorBound (stored.step_mode mode) accepted
    exact ⟨_, .step called, stored.advance mode _, fun _ => outputs, advance_retains stored _, advance_atomic stored mode _,
      advance_storage stored _⟩
  | rejected reason selection selected =>
    rename_i request outputs
    obtain ⟨_, _, _, _, _, _, rejected, _⟩ := prepared.rejections _ literalBase firstBlock signed objects heap literals
    obtain ⟨logger, logging, loggerValue, loggingValue, quiet⟩ := suppressed
    have reads := stored.rejection_reads header _ _ header.nearest reason selection selected
    have called := rejected E program reason p request.flag range logger logging actual (fun _ => rounding)
      (fun _ _ => floorBound) rfl reads selected (fun _ => stored.reset.mode) loggerValue loggingValue quiet
    exact ⟨_, .step called, stored.reject header _ _ header.nearest reason selection selected,
      (by intro zero; cases reason <;> simp [StepRejections.status] at zero),
      reject_retains stored header _ _ header.nearest reason selection selected,
      StepRejections.after_atomic reason _ heap p reads selected stored.reset,
      StepRejections.after_storage reason _ heap p reads selected stored.reset⟩
  | restart admissible =>
    obtain ⟨entered, exited⟩ := InitializationEnvironment.calls header objects (pool.addresses firstBlock) model
      program (Reset.finalHeap heap p) p _ .cs enterDefined exitDefined admissible
      (StaticReset.entry_storage heap p) ((StaticReset.kind_value heap p).trans stored.kind)
    exact ⟨_, .restart (reset.successful heap p .cs before.mode stored.reset stored.kind stored.mode)
      entered exited, stored.restart _ admissible, True.intro, restart_retains heap p _, restart_atomic stored.reset _,
      InitializationStorage.restarted model heap p .cs before.mode stored.reset stored.kind stored.mode _ admissible⟩

inductive ReferenceTrace (header : CFenv.Header) (p : Address) (buffers : StepEntry.Buffers) :
    Reference → List Action → Reference → List Int → Prop where
  | nil : ReferenceTrace header p buffers reference [] reference []
  | cons {before next final : Reference} {action : Action} {rest : List Action} {status : Int} {statuses : List Int} :
      Change header p buffers before action next status → ReferenceTrace header p buffers next rest final statuses →
      ReferenceTrace header p buffers before (action :: rest) final (status :: statuses)

/-- Each intermediate run state retains its exact Solve value, time, mode,
stop policy and writable recovery storage, together with the actual call. -/
inductive Calls [CInterface] (model : Solve.Model source) (program : Events.Program E)
    (p : Address) (buffers : StepEntry.Buffers) :
    Heap → Reference → List Action → Heap → Reference → List Int → Prop where
  | nil : Calls model program p buffers heap reference [] heap reference []
  | cons {heap after finalHeap : Heap} {before next final : Reference}
      {action : Action} {rest : List Action} {status : Int} {statuses : List Int} :
      Executed program p heap action after status → Stored model after p buffers next →
      Observation buffers next action status after →
      (CStorage.Preserves heap after ∧ CAtomicBoolean.Preserves heap after ∧ Retains p heap after) →
      Calls model program p buffers after next rest finalHeap final statuses →
      Calls model program p buffers heap before (action :: rest) finalHeap final (status :: statuses)

/-- Arbitrarily interleaved admitted steps, rejected calls and reset/restart
sequences derive every later heap from the original storage. Error mode prevents
accepted steps until recovery; reset selects a new source epoch. -/
theorem trace_correct (header : CFenv.Header) (objects : Objects)
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
      CAtomicBoolean.Preserves heap after := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program range actual rounding floorBound reset enterDefined exitDefined heap before final actions statuses
    literals stored quiet trace
  induction trace generalizing heap with
  | nil => exact ⟨heap, .nil, stored, fun _ _ => rfl, .refl _, .refl _⟩
  | cons changed _ ih =>
    obtain ⟨next, called, nextStored, observed, retained, atomic, storage⟩ := change_correct header objects model signatures pool prepared literalBase firstBlock
      signed p buffers program range actual rounding floorBound reset enterDefined exitDefined heap _ _ _ _ literals stored quiet changed
    obtain ⟨after, calls, finalStored, retainedAfter, readonly, atomicAfter⟩ := ih next (literals.trans called.readonly)
      nextStored (retained.suppressed quiet)
    exact ⟨after, .cons called nextStored observed ⟨storage, atomic, retained⟩ calls, finalStored, retained.trans retainedAfter,
      called.readonly.trans readonly, atomic.trans atomicAfter⟩

end Rumoca.FMI3.CSRun
end
