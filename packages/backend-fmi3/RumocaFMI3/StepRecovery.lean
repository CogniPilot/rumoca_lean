import RumocaFMI3.ResetStorage
import RumocaFMI3.ResetEnvironment
import RumocaFMI3.StepContract

noncomputable section
namespace Rumoca.FMI3.StepRejections
open CTree CMemory StaticFactory

/-- Every rejected public call preserves instance cells except for the
defined error-mode write. This is the state before any foreign logger effect. -/
theorem after_frame (reason : Reason) (query : StepCases.Query) (heap : Heap) (p : Address)
    (reads : Reads reason query heap p) (selected : StepCases.Condition query reason.outcome)
    (address : Address) (inside : address.block = p.block) (notMode : address ≠ p.member "mode") :
    afterHeap reason query heap p address = heap address := by
  unfold afterHeap
  split
  · exact before_frame reason query heap p reads selected address inside
  · exact (LifecycleBodies.write_frame _ p address .terminated notMode).trans
      (before_frame reason query heap p reads selected address inside)

def nextMode (reason : Reason) (mode : Mode) : Mode := if reason = .discard then mode else .terminated

theorem after_kind (reason : Reason) (query : StepCases.Query) (heap : Heap) (p : Address)
    (reads : Reads reason query heap p) (selected : StepCases.Condition query reason.outcome) :
    load (afterHeap reason query heap p) (p.member "kind") = some (.integer query.kind.code) := by
  simpa only [load, after_frame reason query heap p reads selected (p.member "kind") rfl (by simp)] using reads.kind

theorem after_mode (reason : Reason) (query : StepCases.Query) (heap : Heap) (p : Address)
    (reads : Reads reason query heap p) (selected : StepCases.Condition query reason.outcome) :
    load (afterHeap reason query heap p) (p.member "mode") = some (.integer (nextMode reason query.mode).code) := by
  by_cases discard : reason = .discard
  · simp only [afterHeap, nextMode, if_pos discard]
    exact (before_load reason query heap p reads selected "mode").trans reads.mode
  · simp only [afterHeap, nextMode, if_neg discard]
    exact LifecycleBodies.write_mode _ p .terminated

/-- Reset's full writable-instance premise survives every classified
rejection. A separate callback frame is required after enabled logging. -/
theorem after_reset_storage (reason : Reason) (query : StepCases.Query) (heap : Heap) (p : Address)
    (reads : Reads reason query heap p) (selected : StepCases.Condition query reason.outcome)
    (storage : Reset.Storage heap p) : Reset.Storage (afterHeap reason query heap p) p := by
  have field (name : String) (other : name ≠ "mode") (type : CType)
      (stored : Reset.Writable heap (p.member name) type) :
      Reset.Writable (afterHeap reason query heap p) (p.member name) type := by
    obtain ⟨value, found⟩ := stored
    exact ⟨value, (after_frame reason query heap p reads selected (p.member name) rfl
      (by simpa using other)).trans found⟩
  refine ⟨?_, field "time" (by decide) _ storage.time,
    field "timeMin" (by decide) _ storage.minimum, field "eventTime" (by decide) _ storage.event,
    field "lastCompleted" (by decide) _ storage.completed, field "stop" (by decide) _ storage.stop,
    field "stopDefined" (by decide) _ storage.stopDefined, ?_⟩
  · obtain ⟨value, found⟩ := storage.state
    exact ⟨value, (after_frame reason query heap p reads selected (StateProofs.stateAddress p) rfl
      (HistoryBodies.state_ne_field p "mode")).trans found⟩
  · by_cases discard : reason = .discard
    · obtain ⟨value, found⟩ := storage.mode
      exact ⟨value, by simpa only [afterHeap, if_pos discard] using
        (before_frame reason query heap p reads selected (p.member "mode") rfl).trans found⟩
    · exact ⟨some (.integer Mode.terminated.code), by simp [afterHeap, discard, LifecycleBodies.writeMode]⟩

/-- Suppressed Error/Discard can be followed by the actual reset call from
the original instance's storage, without assuming any post-error heap. -/
theorem reset_after [CInterface] (program : CCalls.Events.Program E)
    (reset : StaticReset.ExecutionContract program) (reason : Reason) (query : StepCases.Query)
    (heap : Heap) (p : Address) (reads : Reads reason query heap p)
    (selected : StepCases.Condition query reason.outcome) (storage : Reset.Storage heap p) :
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling Reset.signature.name [.pointer (some p)] (afterHeap reason query heap p) .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, Reset.finalHeap (afterHeap reason query heap p) p⟩ :=
  reset.successful _ p query.kind (nextMode reason query.mode)
    (after_reset_storage reason query heap p reads selected storage)
    (after_kind reason query heap p reads selected) (after_mode reason query heap p reads selected)

end Rumoca.FMI3.StepRejections


namespace Rumoca.FMI3.StepRejections
open CTree CMemory StaticFactory

/-- Typed output/mode writes cannot alias existing atomic reservation cells.
Every rejection preserves the leases before any foreign logger executes. -/
theorem after_atomic (reason : Reason) (query : StepCases.Query) (heap : Heap) (p : Address)
    (reads : Reads reason query heap p) (selected : StepCases.Condition query reason.outcome)
    (storage : Reset.Storage heap p) : CAtomicBoolean.Preserves heap (afterHeap reason query heap p) := by
  intro address busy atomic
  have different (target : Address) (type : CType) (nonatomic : type ≠ .atomicBoolean)
      (typed : Reset.Writable heap target type) : address ≠ target := by
    obtain ⟨value, found⟩ := typed
    intro same
    rw [same] at atomic
    exact nonatomic (congrArg Cell.type (Option.some.inj (atomic.symm.trans found))).symm
  have before : beforeHeap reason query heap address = heap address := by
    by_cases writes : reason.writesOutputs = true
    · obtain ⟨buffers, outputs⟩ := buffers_present reason query selected writes
      have stored := reads.outputs writes buffers outputs
      simp only [beforeHeap, writes, ↓reduceIte, outputHeap_of_buffers query heap buffers outputs]
      exact StepEntry.output_frame heap buffers query.time address
        (different _ _ (by intro h; cases h) stored.event)
        (different _ _ (by intro h; cases h) stored.terminate)
        (different _ _ (by intro h; cases h) stored.early)
        (different _ _ (by intro h; cases h) stored.last)
    · simp [beforeHeap, writes]
  unfold afterHeap
  split
  · exact before.trans atomic
  · exact (LifecycleBodies.write_frame _ p address .terminated
      (different _ _ (by intro h; cases h) storage.mode)).trans (before.trans atomic)

/-- Suppressed rejection followed by reset and initialization retains the
original owner map. Enabled logger effects require their own lease frame. -/
theorem restarted_owners (objects : Objects) (reason : Reason) (query : StepCases.Query)
    (heap : Heap) (slot : Fin objects.capacity) (args : Initialization.Arguments)
    (owners : SlotOwners.State objects.capacity)
    (reads : Reads reason query heap (objects.instances.index slot.val))
    (selected : StepCases.Condition query reason.outcome)
    (storage : Reset.Storage heap (objects.instances.index slot.val))
    (represented : SlotOwners.Represents objects.flagsBlock heap owners) :
    SlotOwners.Represents objects.flagsBlock
      (InitializationCalls.exitedHeap
        (Reset.finalHeap (afterHeap reason query heap (objects.instances.index slot.val)) (objects.instances.index slot.val))
        (objects.instances.index slot.val) args query.kind) owners :=
  StaticReset.restarted_owners objects _ slot args query.kind owners
    (SlotOwners.ordinary_preserves represented (after_atomic reason query heap _ reads selected storage))

theorem restarted_metadata (reason : Reason) (query : StepCases.Query) (heap : Heap) (p : Address)
    (args : Initialization.Arguments) (reads : Reads reason query heap p)
    (selected : StepCases.Condition query reason.outcome) :
    load (InitializationCalls.exitedHeap (Reset.finalHeap (afterHeap reason query heap p) p) p args query.kind)
      (p.member "slot") = load heap (p.member "slot") := by
  rw [StaticInitialization.exited_metadata, StaticReset.metadata]
  simp only [load, after_frame reason query heap p reads selected (p.member "slot") rfl (by simp)]

end Rumoca.FMI3.StepRejections
end
