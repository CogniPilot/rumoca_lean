import RumocaFMI3.InitializationSimulation
import RumocaFMI3.MEMixedExecution
import RumocaFMI3.MEMixedProgress

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CMemory StaticFactory CCalls.Events

theorem me_field_outside (stored : MENumericalHistory.Stored heap p clock reference addresses buffer)
    (name : String) (retained : name ∉ ["time", "timeMin", "eventTime", "lastCompleted", "stop", "stopDefined", "mode"]) :
    MENumericalRun.Outside p addresses buffer (p.member name) := by
  have different (field : String)
      (member : field ∈ ["time", "timeMin", "eventTime", "lastCompleted", "stop", "stopDefined", "mode"]) :
      p.member name ≠ p.member field := by
    intro same
    exact retained ((Address.member_inj _ _ _).mp same ▸ member)
  have outputs : ∀ label ∈ DiscreteCalls.names, p.member name ≠ addresses label := by
    intro label declared same
    exact stored.control.outside label declared (by simpa using (congrArg Address.block same).symm)
  exact ⟨⟨⟨different "time" (by simp), different "mode" (by simp), different "eventTime" (by simp),
    different "timeMin" (by simp), different "lastCompleted" (by simp), outputs⟩,
    Ne.symm (HistoryBodies.state_ne_field p name), stored.field_ne_buffer name⟩,
    different "stop" (by simp), different "stopDefined" (by simp)⟩

/-- ME simulation derives every resource needed by a later initialization
from the original caller bank and the universal logging policy. -/
structure MEExecution [CInterface] (model : Solve.FMI3Model source) (program : Program Invocation)
    (objects : Objects) (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (original literals heap : Heap) (p : Address) (addresses : String → Address) (buffer : Address)
    (before : MENumericalHistory.ReferenceState) (clock : Time.Clock) (actions : List MEMixedRun.Action)
    (final : MENumericalHistory.ReferenceState) (finalClock : Time.Clock) : Prop where
  trace : ∃ config, MEMixedRun.Trace model objects owners config program p addresses buffer heap before clock actions final finalClock
  progress : (∃ observed after epochs, MEMixedRun.Completed program p addresses buffer heap actions observed after epochs) ∨
    MEMixedRun.Stopped program p addresses buffer heap actions
  completed : ∀ observed after epochs, MEMixedRun.Completed program p addresses buffer heap actions observed after epochs →
    MENumericalHistory.Stored after p finalClock final addresses buffer ∧ Reset.Storage after p ∧
    Persistent program objects retained owners original literals after p ∧
    Retains p heap after ∧ CReadOnly.Preserves heap after ∧
    (∀ q, MEFailure.Protected objects addresses buffer q → MENumericalRun.Outside p addresses buffer q → after q = heap q)
  faulted : ∀ action rest, actions = action :: rest → MEMixedRun.Faulted program p addresses buffer heap action →
    action.Rejection

theorem me_execution (header : CFenv.Header) (objects : Objects) (model : Solve.FMI3Model source)
    (sigs : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap CLiteral.functionNames))
    (prepared : MEEnvironment.PreparedContract model sigs pool)
    (counts : ∀ events, CountEnvironment.PreparedContract model sigs events pool)
    (nominals : NominalEnvironment.PreparedContract model sigs pool)
    (lifecycle : LifecycleEnvironment.PreparedContract model sigs)
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation), program.internal = LiteralPreparation.program model sigs →
    ∀ (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
      (original heap : Heap) (p : Address) (addresses : String → Address) (buffer : Address)
      (before final : MENumericalHistory.ReferenceState) (clock finalClock : Time.Clock) (actions : List MEMixedRun.Action),
      Persistent program objects retained owners original (pool.install baseHeap firstBlock signed) heap p →
      p.block = objects.instances.block → MEOutputsGuarded objects retained addresses buffer →
      MENumericalHistory.Stored heap p clock before addresses buffer → Reset.Storage heap p →
      MEMixedRun.ReferenceTrace buffer before clock actions final finalClock →
      (∀ action ∈ actions, action.Prepared objects original addresses buffer) →
      (∀ action ∈ actions, ∀ q, action.CallerRegion q → Float64Rejection.Protected objects retained q) →
      MEExecution model program objects retained owners original (pool.install baseHeap firstBlock signed)
        heap p addresses buffer before clock actions final finalClock := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual retained owners original heap p addresses buffer before final clock finalClock actions
    persistent inPool guarded stored resetStorage admitted requests regions
  obtain ⟨config, configured, valid, policy⟩ := persistent.logging.me guarded
  obtain ⟨reset, enterDefined, exitDefined, _, _⟩ := lifecycle.execution header objects (pool.addresses firstBlock) program actual
  have current : ∀ action ∈ actions, action.Prepared objects heap addresses buffer := by
    intro action member
    exact MEMixedRun.Action.Prepared.preserved action (requests action member)
      (fun q inside => persistent.caller q (regions action member q inside))
  have policies := fun action member => policy.mono (regions action member)
  have certified := MEMixedRun.trace_correct header objects model sigs pool prepared counts nominals baseHeap firstBlock signed program config
    actual reset enterDefined exitDefined heap p clock before final finalClock addresses buffer actions owners valid configured
    inPool persistent.ownership persistent.readonly stored resetStorage admitted current policies
  refine ⟨⟨config, certified⟩, certified.progress, ?_, ?_⟩
  · intro observed after epochs completed
    obtain ⟨nextStored, nextReset, _, ownersAfter, readonly, frame⟩ := certified.completed completed
    have keeps : Retains p heap after := fun name retained =>
      frame (p.member name) (Or.inl (by simpa using inPool)) (me_field_outside stored name retained)
    exact ⟨nextStored, nextReset,
      ⟨ownersAfter, persistent.caller.trans (certified.storage completed policy), persistent.readonly.trans readonly,
        persistent.logging.framed keeps⟩, keeps, readonly, frame⟩
  · intro action rest same faulted
    cases same
    cases certified with
    | cons called _ _ => exact called.faulted_rejection faulted

end Rumoca.FMI3.InitializationProtocol
end
