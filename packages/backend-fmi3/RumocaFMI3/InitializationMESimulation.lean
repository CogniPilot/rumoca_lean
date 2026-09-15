import RumocaFMI3.InitializationSimulation
import RumocaFMI3.MEMixedExecution
import RumocaFMI3.MEMixedProgress

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CMemory StaticFactory CCalls.Events

/-- ME simulation derives every resource needed by a later initialization
from the original caller bank and the universal logging policy. -/
structure MEExecution [CInterface] (model : Solve.FMI3Model source) (program : Program Invocation)
    (objects : Objects) (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (original literals heap : Heap) (p : Address) (addresses : String → Address) (buffer : Address)
    (before : MENumericalHistory.ReferenceState) (clock : Time.Clock) (actions : List MEMixedRun.Action)
    (final : MENumericalHistory.ReferenceState) (finalClock : Time.Clock) (readers : ReadBank) : Prop where
  trace : ∃ capability enabled, capability.Configured heap p enabled ∧
    MEMixedRun.Trace model objects owners capability program p addresses buffer heap enabled before clock actions final finalClock
  progress : (∃ observed after epochs, MEMixedRun.Completed program p addresses buffer heap actions observed after epochs) ∨
    MEMixedRun.Stopped program p addresses buffer heap actions
  completed : ∀ observed after epochs, MEMixedRun.Completed program p addresses buffer heap actions observed after epochs →
    MENumericalHistory.Stored after p finalClock final addresses buffer ∧ Reset.Storage after p ∧
    Persistent program objects retained owners original literals after p readers ∧
    Retention (MEMixedRun.loggingUpdate actions) p heap after ∧ CReadOnly.Preserves heap after ∧
    (∀ q, MEFailure.Protected objects addresses buffer q → MENumericalRun.Outside p addresses buffer q →
      q ≠ p.member "logging" → after q = heap q)
  faulted : ∀ action rest, actions = action :: rest → MEMixedRun.Faulted program p addresses buffer heap action →
    action.Rejection

theorem me_execution (header : CFenv.Header) (objects : Objects) (model : Solve.FMI3Model source)
    (sigs : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap CLiteral.functionNames))
    (prepared : MEEnvironment.PreparedContract model sigs pool)
    (counts : ∀ events, CountEnvironment.PreparedContract model sigs events pool)
    (nominals : NominalEnvironment.PreparedContract model sigs pool)
    (logging : DebugLogging.PreparedContract model sigs pool)
    (lifecycle : LifecycleEnvironment.PreparedContract model sigs)
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation), program.internal = LiteralPreparation.program model sigs →
    program.externals "strcmp" = some (CStringCalls.compareExternal (by rfl)) →
    ∀ (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
      (original heap : Heap) (p : Address) (addresses : String → Address) (buffer : Address)
      (before final : MENumericalHistory.ReferenceState) (clock finalClock : Time.Clock) (actions : List MEMixedRun.Action) (readers : ReadBank),
      Persistent program objects retained owners original (pool.install baseHeap firstBlock signed) heap p readers →
      p.block = objects.instances.block → MEOutputsGuarded objects retained addresses buffer →
      (∀ q, readers.Region q → Float64Rejection.Protected objects retained q ∧ MENumericalRun.Outside p addresses buffer q ∧ q ≠ p.member "logging") →
      (∀ action ∈ actions, ∀ q, readers.Region q → ¬ action.CallerRegion q) →
      MENumericalHistory.Stored heap p clock before addresses buffer → Reset.Storage heap p →
      MEMixedRun.ReferenceTrace buffer before clock actions final finalClock →
      (∀ action ∈ actions, action.Prepared objects original addresses buffer) →
      (∀ action ∈ actions, ∀ q, action.CallerRegion q → Float64Rejection.Protected objects retained q) →
      (∀ action ∈ actions, ∀ q, action.ReaderRegion q → readers.Region q) →
      MEExecution model program objects retained owners original (pool.install baseHeap firstBlock signed)
        heap p addresses buffer before clock actions final finalClock readers := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual compare retained owners original heap p addresses buffer before final clock finalClock actions readers
    persistent inPool guarded readerGuarded readerSafe stored resetStorage admitted requests regions included
  obtain ⟨capability, enabled, configured, bound, required, writable⟩ := persistent.logging
  obtain ⟨reset, enterDefined, exitDefined, _, _⟩ := lifecycle.execution header objects (pool.addresses firstBlock) program actual
  have memoryPolicy (region : Address → Prop)
      (subset : ∀ q, region q → Float64Rejection.Protected objects retained q) :
      capability.Requires (fun _ effect => ∀ args before value after,
        effect.execute args before value after → CStorage.PreservesOn region before after) := by
    apply Logging.Capability.requires_mono required
    intro name effect respects args before value after executed
    exact CStorage.PreservesOn.of_frame (fun q inside => respects args before value after executed q (subset q inside))
  have exactPolicy (region : Address → Prop)
      (subset : ∀ q, region q → Float64Rejection.Protected objects retained q) :
      capability.Requires (fun _ effect => ∀ args before value after,
        effect.execute args before value after → ∀ q, region q → after q = before q) := by
    apply Logging.Capability.requires_mono required
    exact fun name effect respects args before value after executed q inside =>
      respects args before value after executed q (subset q inside)
  have meRequired : capability.Requires (fun _ effect => MEFailure.Respects effect objects addresses buffer) := by
    apply Logging.Capability.requires_mono required
    exact fun name effect respects args before value after executed q inside =>
      respects args before value after executed q (guarded.protects inside)
  have current : ∀ action ∈ actions, action.Prepared objects heap addresses buffer := by
    intro action member
    exact MEMixedRun.Action.Prepared.preserved action (requests action member)
      (fun q inside => persistent.caller q (regions action member q inside))
      (fun q inside => persistent.readerFrame q (included action member q inside))
  have certified := MEMixedRun.trace_correct header objects model sigs pool prepared counts nominals logging baseHeap firstBlock signed
    program capability enabled actual compare bound reset enterDefined exitDefined heap p clock before final finalClock
    addresses buffer actions owners meRequired configured writable inPool persistent.ownership persistent.readonly
    stored resetStorage admitted current
    (fun action member => memoryPolicy action.CallerRegion (regions action member))
    (fun action member => exactPolicy action.ReaderRegion (fun q inside => (readerGuarded q (included action member q inside)).1))
    (fun action member q inside => (readerGuarded q (included action member q inside)).2)
    (fun writer written reader read q inside => readerSafe writer written q (included reader read q inside))
  refine ⟨⟨capability, enabled, configured, certified⟩, certified.progress, ?_, ?_⟩
  · intro observed after epochs completed
    obtain ⟨nextStored, nextReset, _, keeps, ownersAfter, readonly, frame⟩ := certified.completed completed
    exact ⟨nextStored, nextReset,
      ⟨ownersAfter, persistent.caller.trans (certified.storage completed (memoryPolicy _ (fun _ inside => inside))),
        persistent.readonly.trans readonly, persistent.logging.updated keeps,
        persistent.readerFrame.trans (fun q inside => certified.callerFrame completed
          (exactPolicy readers.Region (fun cell member => (readerGuarded cell member).1))
          q inside (readerGuarded q inside).2.1 (readerGuarded q inside).2.2
          (fun action member => readerSafe action member q inside))⟩,
      keeps, readonly, frame⟩
  · intro action rest same faulted
    cases same
    cases certified with
    | cons called _ _ => exact called.faulted_rejection faulted

end Rumoca.FMI3.InitializationProtocol
end
