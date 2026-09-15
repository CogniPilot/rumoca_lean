import RumocaFMI3.InitializationSimulation
import RumocaFMI3.CSMixedExecution
import RumocaFMI3.CSMixedPrefixes

noncomputable section
namespace Rumoca.FMI3.CSMixedRun
open CTree CMemory StaticFactory CCalls.Events
open InitializationProtocol (Persistent ReadBank)

/-- A mixed CS segment retains the resources needed by later initialization.
Its trace field supplies per-call source records without a second execution path. -/
structure Execution [CInterface] (model : Solve.FMI3Model source) (header : CFenv.Header)
    (program : Program Invocation) (objects : Objects) (retained : Address → Prop)
    (owners : SlotOwners.State objects.capacity) (original literals heap : Heap) (p : Address)
    (buffers : StepEntry.Buffers) (before : CSRun.Reference) (actions : List Action)
    (final : CSRun.Reference) (statuses : List Int) (readers : ReadBank) : Prop where
  trace : ∃ capability enabled, capability.Configured heap p enabled ∧
    Trace header objects owners model.solve capability program p buffers heap enabled before actions final statuses
  progress : (∃ observed events after, Completed program p heap actions observed events after) ∨ Stopped program p heap actions
  completed : ∀ observed events after, Completed program p heap actions observed events after →
    observed = statuses.map Value.integer ∧ CSRun.Stored model.solve after p buffers final ∧
    Persistent program objects retained owners original literals after p readers ∧
    InitializationProtocol.Retention (loggingUpdate actions) p heap after ∧ CReadOnly.Preserves heap after ∧
    (∀ q, CSRun.Protected objects buffers q → CSRun.Outside p buffers q → after q = heap q)
  faulted : ∀ action rest, actions = action :: rest → Faulted program p heap action → action.MayBlock

/-- The original initialization capability and borrowed-input bank provide
every later simulation precondition. Successful logging updates are composed
back into the same persistent capability for a subsequent reset/handoff. -/
theorem execution (header : CFenv.Header) (objects : Objects) (model : Solve.FMI3Model source)
    (sigs : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap CLiteral.functionNames))
    (prepared : CSRunEnvironment.PreparedContract model sigs pool)
    (logging : DebugLogging.PreparedContract model sigs pool)
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation) (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
      program.internal = LiteralPreparation.program model sigs →
      program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
      program.externals "floor" = some (CMathCalls.floorExternal rfl) →
      program.externals "strcmp" = some (CStringCalls.compareExternal rfl) →
    ∀ (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
      (original heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
      (before final : CSRun.Reference) (actions : List Action) (statuses : List Int) (readers : ReadBank),
      Persistent program objects retained owners original (pool.install baseHeap firstBlock signed) heap p readers →
      p.block = objects.instances.block → InitializationProtocol.CSOutputsGuarded objects retained buffers →
      (∀ q, readers.Region q → Float64Rejection.Protected objects retained q ∧ CSRun.Outside p buffers q) →
      CSRun.Stored model.solve heap p buffers before → ReferenceTrace header p buffers before actions final statuses →
      (∀ action ∈ actions, action.Prepared original) →
      (∀ action ∈ actions, ∀ q, action.ReaderRegion q → readers.Region q) →
      Execution model header program objects retained owners original (pool.install baseHeap firstBlock signed)
        heap p buffers before actions final statuses readers := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program range actual rounding floorBound compare retained owners original heap p buffers before final actions statuses readers
    persistent inPool guarded readerGuarded stored admitted requests included
  obtain ⟨capability, enabled, configured, bound, required, writable⟩ := persistent.logging
  obtain ⟨reset, enterDefined, exitDefined, _, _⟩ := prepared.execution header objects firstBlock program actual
  have memoryPolicy (region : Address → Prop)
      (subset : ∀ q, region q → Float64Rejection.Protected objects retained q) :
      capability.Requires (fun _ effect => ∀ args before value after,
        effect.execute args before value after → CStorage.PreservesOn region before after) := by
    apply Logging.Capability.requires_mono required
    intro name effect respects args before value after performed
    exact CStorage.PreservesOn.of_frame (fun q inside => respects args before value after performed q (subset q inside))
  have exactPolicy (region : Address → Prop)
      (subset : ∀ q, region q → Float64Rejection.Protected objects retained q) :
      capability.Requires (fun _ effect => ∀ args before value after,
        effect.execute args before value after → ∀ q, region q → after q = before q) := by
    apply Logging.Capability.requires_mono required
    exact fun name effect respects args before value after performed q inside =>
      respects args before value after performed q (subset q inside)
  have csRequired : capability.Requires (fun _ effect => ∀ args before value after,
      effect.execute args before value after → CSRun.ProtectedFrame objects buffers before after) := by
    apply Logging.Capability.requires_mono required
    exact fun name effect respects args before value after performed q inside =>
      respects args before value after performed q (guarded.protects inside)
  have current : ∀ action ∈ actions, action.Prepared heap := by
    intro action member
    exact Action.Prepared.framed action (requests action member)
      (fun q inside => persistent.readerFrame q (included action member q inside))
  have certified := trace_correct header objects model sigs pool prepared.step logging baseHeap firstBlock signed p buffers inPool
    program capability enabled range actual rounding floorBound compare bound csRequired reset enterDefined exitDefined
    heap before final actions statuses owners persistent.readonly stored configured writable persistent.ownership admitted current
    (fun action member => exactPolicy action.ReaderRegion (fun q inside => (readerGuarded q (included action member q inside)).1))
    (fun action member q inside => (readerGuarded q (included action member q inside)).2)
  refine ⟨⟨capability, enabled, configured, certified⟩, certified.progress, ?_, ?_⟩
  · intro observed events after completed
    obtain ⟨values, nextStored, _, keeps, ownership, readonly, frame⟩ := certified.completed completed
    exact ⟨values, nextStored,
      ⟨ownership, persistent.caller.trans (certified.storage completed (memoryPolicy _ (fun _ inside => inside))),
        persistent.readonly.trans readonly, persistent.logging.updated keeps,
        persistent.readerFrame.trans (fun q inside => certified.callerFrame completed
          (exactPolicy readers.Region (fun q inside => (readerGuarded q inside).1)) q inside (readerGuarded q inside).2)⟩,
      keeps, readonly, frame⟩
  · intro action rest same actual
    cases same
    cases certified with
    | cons _ called _ _ => exact called.faulted_kind actual

end Rumoca.FMI3.CSMixedRun
end
