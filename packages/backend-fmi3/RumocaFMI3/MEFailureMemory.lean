import RumocaFMI3.MENumericalRestart
import RumocaFMI3.StepRecovery

noncomputable section
namespace Rumoca.FMI3.MENumericalHistory
open CTree CMemory CBody StaticFactory

def ReferenceState.failed (reference : ReferenceState) : ReferenceState :=
  { reference with control := { reference.control with mode := .terminated, eventReady := false } }

/-- The error helper changes the lifecycle mode before logging. Retained
numerical storage supports recovery; it does not validate failed-call outputs. -/
theorem Stored.failed (stored : Stored heap p clock reference addresses buffer) :
    Stored (LifecycleBodies.writeMode heap p .terminated) p clock reference.failed addresses buffer := by
  have field (name : String) (different : name ≠ "mode") :
      load (LifecycleBodies.writeMode heap p .terminated) (p.member name) = load heap (p.member name) := by
    simp only [load, LifecycleBodies.write_frame heap p (p.member name) .terminated (by simpa using different)]
  have outputs : MEHistory.Buffers (LifecycleBodies.writeMode heap p .terminated) addresses := by
    apply stored.control.buffers.transport
    intro layout member
    exact LifecycleBodies.write_frame heap p (addresses layout.1) .terminated
      (stored.control.outside.field layout member "mode")
  obtain ⟨old, bufferCell⟩ := stored.bufferCell
  refine ⟨⟨(field "kind" (by decide)).trans stored.control.kind, ?_,
    LifecycleBodies.write_history stored.control.clockStored .terminated, stored.control.history,
    LifecycleBodies.write_model stored.control.modelStored .terminated,
    (field "stopDefined" (by decide)).trans stored.control.stopDefined,
    fun stop chosen => (field "stop" (by decide)).trans (stored.control.stopValue stop chosen), outputs, stored.control.outside⟩,
    (LifecycleBodies.write_frame heap p (StateProofs.stateAddress p) .terminated
      (HistoryBodies.state_ne_field p "mode")).trans stored.stateCell,
    ⟨old, (LifecycleBodies.write_frame heap p buffer .terminated (Ne.symm (stored.field_ne_buffer "mode"))).trans bufferCell⟩,
    stored.bufferOutside, stored.bufferSeparate⟩
  simp [LifecycleBodies.writeMode, ReferenceState.failed]

theorem Stored.failed_reset (stored : Stored heap p clock reference addresses buffer)
    (storage : Reset.Storage heap p) : Reset.Storage (LifecycleBodies.writeMode heap p .terminated) p := by
  apply stored.failed.reset_storage
  · obtain ⟨old, cell⟩ := storage.stop
    exact ⟨old, (LifecycleBodies.write_frame heap p (p.member "stop") .terminated (by simp)).trans cell⟩
  · obtain ⟨old, cell⟩ := storage.stopDefined
    exact ⟨old, (LifecycleBodies.write_frame heap p (p.member "stopDefined") .terminated (by simp)).trans cell⟩

theorem Stored.failed_atomic (stored : Stored heap p clock reference addresses buffer) :
    CAtomicBoolean.Preserves heap (LifecycleBodies.writeMode heap p .terminated) :=
  CAtomicBoolean.replace_nonatomic stored.control.mode (by intro h; cases h) _

/-- A callback frame protects the instance and reusable caller buffers.
Private foreign memory can change independently of these cells. -/
def Frame (p : Address) (addresses : String → Address) (buffer : Address) (before after : Heap) : Prop :=
  ∀ q, p.InRecord q ∨ q = buffer ∨ (∃ name ∈ DiscreteCalls.names, q = addresses name) → after q = before q

theorem Stored.framed (stored : Stored heap p clock reference addresses buffer)
    (frame : Frame p addresses buffer heap after) : Stored after p clock reference addresses buffer := by
  have fields (name : String) := frame (p.member name) (Or.inl (p.member_in_record name))
  have field (name : String) : load after (p.member name) = load heap (p.member name) := by
    simp only [load, fields name]
  have state := frame (StateProofs.stateAddress p) (Or.inl ((p.member_in_record "model").member "x"))
  obtain ⟨old, cell⟩ := stored.bufferCell
  refine ⟨⟨(field "kind").trans stored.control.kind, (fields "mode").trans stored.control.mode,
    ⟨(fields "time").trans stored.control.clockStored.time,
      (fields "timeMin").trans stored.control.clockStored.minimum,
      (fields "eventTime").trans stored.control.clockStored.eventTime,
      (fields "lastCompleted").trans stored.control.clockStored.lastCompleted⟩,
    stored.control.history, ?_, (field "stopDefined").trans stored.control.stopDefined,
    fun stop chosen => (field "stop").trans (stored.control.stopValue stop chosen), ?_, stored.control.outside⟩,
    state.trans stored.stateCell, ⟨old, (frame buffer (Or.inr (Or.inl rfl))).trans cell⟩,
    stored.bufferOutside, stored.bufferSeparate⟩
  · simpa only [StateProofs.Represents, load, state] using stored.control.modelStored
  · apply stored.control.buffers.transport
    intro layout member
    exact frame _ (Or.inr (Or.inr ⟨layout.1, List.mem_map.mpr ⟨layout, member, rfl⟩, rfl⟩))

theorem Frame.reset_storage (frame : Frame p addresses buffer before after)
    (stored : Reset.Storage before p) : Reset.Storage after p :=
  stored.record_preserved (fun q inside => frame q (Or.inl inside))

end Rumoca.FMI3.MENumericalHistory

namespace Rumoca.FMI3.MEFailure
open CTree CMemory StaticFactory

def Protected (objects : Objects) (addresses : String → Address) (buffer q : Address) : Prop :=
  q.block = objects.instances.block ∨ q.block = objects.flagsBlock ∨
    q = buffer ∨ (∃ name ∈ DiscreteCalls.names, q = addresses name)

def ProtectedFrame (objects : Objects) (addresses : String → Address) (buffer : Address)
    (before after : Heap) : Prop :=
  ∀ q, Protected objects addresses buffer q → after q = before q

theorem ProtectedFrame.numerical (frame : ProtectedFrame objects addresses buffer before after)
    (inPool : p.block = objects.instances.block) : MENumericalHistory.Frame p addresses buffer before after := by
  intro q inside
  rcases inside with record | caller | output
  · exact frame q (Or.inl (record.1.trans inPool))
  · exact frame q (Or.inr (Or.inr (Or.inl caller)))
  · exact frame q (Or.inr (Or.inr (Or.inr output)))

theorem ProtectedFrame.owners {owners : SlotOwners.State objects.capacity} (frame : ProtectedFrame objects addresses buffer before after)
    (represented : SlotOwners.Represents objects.flagsBlock before owners) :
    SlotOwners.Represents objects.flagsBlock after owners :=
  fun slot => (frame (AtomicSlots.address objects.flagsBlock slot) (Or.inr (Or.inl rfl))).trans (represented slot)

/-- This is an external contract over every effect outcome and every input
heap, not an assumption that a chosen callback succeeds or returns at all. -/
def Respects [CInterface] (effect : CCalls.Events.ReturningEffect (Logging.signature name))
    (objects : Objects) (addresses : String → Address) (buffer : Address) : Prop :=
  ∀ args before value after, effect.execute args before value after → ProtectedFrame objects addresses buffer before after

theorem Respects.returned [CInterface] {owners : SlotOwners.State objects.capacity} {effect : CCalls.Events.ReturningEffect (Logging.signature name)}
    (policy : Respects effect objects addresses buffer)
    (stored : MENumericalHistory.Stored heap p clock reference addresses buffer)
    (storage : Reset.Storage heap p) (inPool : p.block = objects.instances.block)
    (represented : SlotOwners.Represents objects.flagsBlock heap owners)
    (called : effect.execute args (LifecycleBodies.writeMode heap p .terminated) value after) :
    MENumericalHistory.Stored after p clock reference.failed addresses buffer ∧ Reset.Storage after p ∧
    SlotOwners.Represents objects.flagsBlock after owners ∧
    (∀ q, Protected objects addresses buffer q → q ≠ p.member "mode" → after q = heap q) := by
  have frame := policy _ _ _ _ called
  have numerical := frame.numerical inPool
  exact ⟨stored.failed.framed numerical, numerical.reset_storage (stored.failed_reset storage),
    frame.owners (SlotOwners.ordinary_preserves represented stored.failed_atomic),
    fun q guarded other => (frame q guarded).trans (LifecycleBodies.write_frame heap p q .terminated other)⟩

end Rumoca.FMI3.MEFailure
end
