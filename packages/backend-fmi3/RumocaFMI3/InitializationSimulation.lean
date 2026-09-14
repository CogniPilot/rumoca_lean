import RumocaFMI3.InitializationProtocolRunFrames
import RumocaFMI3.CSRunLoggedExecution
import RumocaFMI3.CSRunProgress
import RumocaFMI3.CSRunEnvironment

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CMemory StaticFactory CCalls.Events

/-- Resources shared by initialization and simulation. The original caller
bank and literal heap stay fixed across every reset and handoff. -/
structure Persistent [CInterface] (program : Program Invocation) (objects : Objects)
    (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (original literals heap : Heap) (p : Address) : Prop where
  ownership : SlotOwners.Represents objects.flagsBlock heap owners
  caller : CallerStorage objects retained original heap
  readonly : CReadOnly.Preserves literals heap
  logging : LogPolicy program objects retained heap p

theorem Invariant.persistent [CInterface] {program : Program Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity}
    (invariant : Invariant program objects retained owners original literals heap p kind state) :
    Persistent program objects retained owners original literals heap p :=
  ⟨invariant.ownership, invariant.caller, invariant.readonly, invariant.logging⟩

/-- The initialization logger policy supplies the simulation policy at the
actual handoff heap. No configuration from the first factory heap is needed. -/
theorem LogPolicy.cs [CInterface] {program : Program Invocation}
    (logging : LogPolicy program objects retained heap p)
    (guarded : CSOutputsGuarded objects retained buffers) :
    CSRun.Suppressed heap p ∨ ∃ logger : CSRun.Logger,
      logger.Stored heap p ∧ logger.Bound program ∧ logger.Respects objects buffers ∧
      logger.StoragePolicy (Float64Rejection.Protected objects retained) := by
  rcases logging with quiet |
    ⟨pointer, environment, name, effect, loggerValue, loggingValue, environmentValue, address, external, respects⟩
  · exact Or.inl quiet
  · refine Or.inr ⟨⟨pointer, environment, name, effect⟩,
      ⟨loggerValue, loggingValue, environmentValue⟩, ⟨address, external⟩, ?_, ?_⟩
    · intro args before value after returned q inside
      exact respects args before value after returned q (guarded.protects inside)
    · intro args before value after returned
      exact CStorage.PreservesOn.of_frame (respects args before value after returned)

theorem LogPolicy.me [CInterface] {program : Program Invocation}
    (logging : LogPolicy program objects retained heap p)
    (guarded : MEOutputsGuarded objects retained addresses buffer) :
    ∃ config : MEMixedRun.Configuration, config.Stored heap p ∧ config.Valid program objects addresses buffer ∧
      config.StoragePolicy (Float64Rejection.Protected objects retained) := by
  rcases logging with ⟨logger, enabled, loggerValue, loggingValue, quiet⟩ |
    ⟨pointer, environment, name, effect, loggerValue, loggingValue, environmentValue, address, external, respects⟩
  · exact ⟨.quiet logger enabled, ⟨loggerValue, loggingValue⟩, quiet, trivial⟩
  · refine ⟨.logged pointer environment name effect,
      ⟨loggerValue, loggingValue, environmentValue⟩, ⟨address, external, ?_⟩, ?_⟩
    · intro args before value after returned q inside
      exact respects args before value after returned q (guarded.protects inside)
    · intro args before value after returned
      exact CStorage.PreservesOn.of_frame (respects args before value after returned)

/-- A simulation segment retains the resources needed for the next
initialization, for every raw completed execution and every logger outcome. -/
structure CSExecution [CInterface] (model : Solve.FMI3Model source) (header : CFenv.Header) (program : Program Invocation)
    (objects : Objects) (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (original literals heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
    (before : CSRun.Reference) (actions : List CSRun.Action) (final : CSRun.Reference) (statuses : List Int) : Prop where
  progress : (∃ events after, CSRun.Completed program p heap actions statuses events after) ∨
    CSRun.Stopped program p heap actions
  completed : ∀ observed events after, CSRun.Completed program p heap actions observed events after →
    observed = statuses ∧ CSRun.Stored model.solve after p buffers final ∧
    Persistent program objects retained owners original literals after p ∧
    CSRun.Retains p heap after ∧ CReadOnly.Preserves heap after ∧
    (∀ q, CSRun.Protected objects buffers q → CSRun.Outside p buffers q → after q = heap q)
  semantic : ∀ observed events after records, CSRun.Recorded program p heap actions observed events after records →
    CSRun.SemanticTrace model.solve header p buffers heap before actions observed records after final

theorem cs_execution (header : CFenv.Header) (objects : Objects) (model : Solve.FMI3Model source)
    (sigs : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap CLiteral.functionNames))
    (prepared : CSRunEnvironment.PreparedContract model sigs pool)
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation) (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
      program.internal = LiteralPreparation.program model sigs →
      program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
      program.externals "floor" = some (CMathCalls.floorExternal rfl) →
    ∀ (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
      (original heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
      (before final : CSRun.Reference) (actions : List CSRun.Action) (statuses : List Int),
      Persistent program objects retained owners original (pool.install baseHeap firstBlock signed) heap p →
      p.block = objects.instances.block → CSOutputsGuarded objects retained buffers →
      CSRun.Stored model.solve heap p buffers before → CSRun.ReferenceTrace header p buffers before actions final statuses →
      CSExecution model header program objects retained owners original (pool.install baseHeap firstBlock signed)
        heap p buffers before actions final statuses := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program range actual rounding floorBound retained owners original heap p buffers before final actions statuses
    persistent inPool guarded stored admitted
  obtain ⟨reset, enterDefined, exitDefined, _, _⟩ := prepared.execution header objects firstBlock program actual
  rcases persistent.logging.cs guarded with quiet | ⟨logger, logging, bound, policy, storagePolicy⟩
  · obtain ⟨after, calls, finalStored, keeps, readonly, atomic, frame, semantic⟩ :=
      CSRun.trace_framed header objects model sigs pool prepared.step baseHeap firstBlock signed p buffers program range
        actual rounding floorBound reset enterDefined exitDefined heap before final actions statuses persistent.readonly stored quiet admitted
    refine ⟨Or.inl ⟨[], after, calls.executes⟩, ?_, semantic⟩
    intro observed events actualAfter completed
    obtain ⟨sameStatuses, _, sameHeap⟩ := calls.determines completed
    subst actualAfter
    exact ⟨sameStatuses, finalStored,
      ⟨SlotOwners.ordinary_preserves persistent.ownership atomic,
        persistent.caller.trans (CallerStorage.ordinary calls.storage), persistent.readonly.trans readonly,
        persistent.logging.framed (fun name outside => keeps name outside)⟩,
      keeps, readonly, fun q _ outside => frame q outside⟩
  · obtain ⟨certified, semantic⟩ := CSRun.logged_trace_correct header objects model sigs pool prepared.step baseHeap firstBlock signed
      p buffers inPool program range logger actual rounding floorBound bound policy reset enterDefined exitDefined
      heap before final actions statuses owners persistent.readonly stored logging persistent.ownership admitted
    refine ⟨certified.progress, ?_, semantic⟩
    intro observed events after completed
    have same := certified.statuses_eq completed
    subst observed
    obtain ⟨finalStored, _, ownership, keeps, readonly, frame⟩ := certified.completed completed
    exact ⟨rfl, finalStored, ⟨ownership, persistent.caller.trans (certified.storage completed storagePolicy),
      persistent.readonly.trans readonly, persistent.logging.framed (fun name outside => keeps name outside)⟩,
      keeps, readonly, frame⟩

end Rumoca.FMI3.InitializationProtocol
end
