import RumocaFMI3.Float64RejectionPreparation
import RumocaFMI3.LifecycleStorage
import RumocaFMI3.ResetStorage
import RumocaFMI3.SlotOwners

noncomputable section
namespace Rumoca.FMI3.Float64Access
open CMemory

variable {kind : Kind} {mode : Mode} {state : ModelExchange.State} {time : Binary64.Value}

theorem Instance.failed (stored : Instance heap p kind mode state time) :
    Instance (LifecycleBodies.writeMode heap p .terminated) p kind .terminated state time := by
  have fields (name : String) (different : name ≠ "mode") :=
    LifecycleBodies.write_frame heap p (p.member name) .terminated (by simpa using different)
  exact ⟨by simpa only [load, fields "kind" (by decide)] using stored.kind,
    by simp [LifecycleBodies.writeMode],
    (LifecycleBodies.write_frame heap p _ .terminated (HistoryBodies.state_ne_field p "mode")).trans stored.state,
    by simpa only [load, fields "time" (by decide)] using stored.time⟩

theorem Instance.record_preserved (stored : Instance heap p kind mode state time)
    (frame : ∀ q, p.InRecord q → after q = heap q) : Instance after p kind mode state time := by
  have fields (name : String) := frame _ (p.member_in_record name)
  exact ⟨by simpa only [load, fields] using stored.kind,
    (fields "mode").trans stored.mode,
    (frame _ ((p.member_in_record "model").member "x")).trans stored.state,
    by simpa only [load, fields] using stored.time⟩

end Rumoca.FMI3.Float64Access

namespace Rumoca.FMI3.Float64Rejection
open CMemory StaticFactory

/-- The host selects the additional caller region to retain across logging.
All instance slots and reservation cells are always protected. This supports
both interfaces and later initialization/simulation buffers without baking a
particular ME or CS output layout into the accessor contract. -/
def Protected (objects : Objects) (retained : Address → Prop) (q : Address) : Prop :=
  q.block = objects.instances.block ∨ q.block = objects.flagsBlock ∨ retained q

def Frame (objects : Objects) (retained : Address → Prop) (before after : Heap) : Prop :=
  ∀ q, Protected objects retained q → after q = before q

theorem Frame.record {p : Address} (frame : Frame objects retained before after)
    (inPool : p.block = objects.instances.block) : ∀ q, p.InRecord q → after q = before q :=
  fun q member => frame q (Or.inl (member.1.trans inPool))

theorem Frame.owners {owners : SlotOwners.State objects.capacity}
    (frame : Frame objects retained before after)
    (represented : SlotOwners.Represents objects.flagsBlock before owners) :
    SlotOwners.Represents objects.flagsBlock after owners :=
  fun slot => (frame _ (Or.inr (Or.inl rfl))).trans (represented slot)

theorem Frame.writable (frame : Frame objects retained before after)
    (stored : ArrayStore.Writable before base type count)
    (guarded : ∀ i < count, Protected objects retained (base.index i)) :
    ArrayStore.Writable after base type count := by
  intro i inside
  obtain ⟨old, cell⟩ := stored i inside
  exact ⟨old, (frame _ (guarded i inside)).trans cell⟩

def Respects [CInterface] (effect : CCalls.Events.ReturningEffect (Logging.signature name))
    (objects : Objects) (retained : Address → Prop) : Prop :=
  ∀ args before value after, effect.execute args before value after → Frame objects retained before after

end Rumoca.FMI3.Float64Rejection
end
