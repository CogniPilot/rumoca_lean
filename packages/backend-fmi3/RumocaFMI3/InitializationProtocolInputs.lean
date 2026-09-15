import RumocaFMI3.InitializationProtocolCalls

/-! Borrowed category arrays and strings are supplied once in the original
heap. Exact call frames preserve them through earlier actions; writable caller
storage is supported, and no future readable heap is an input assumption. -/
noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CMemory StaticFactory

abbrev ReadBank := List DebugLogging.Request

def ReadBank.Region (readers : ReadBank) (q : Address) : Prop :=
  ∃ request ∈ readers, request.Region q

def ReadBank.Stored (readers : ReadBank) (heap : Heap) : Prop :=
  ∀ request ∈ readers, request.Inputs heap

def ReadBank.Frame (readers : ReadBank) (before after : Heap) : Prop :=
  ∀ q, readers.Region q → after q = before q

def ReadBank.Guarded (readers : ReadBank) (objects : Objects) (retained : Address → Prop)
    (p : Address) (buffers : Float64Buffers.Layout) : Prop :=
  ∀ q, readers.Region q → Float64Rejection.Protected objects retained q ∧
    ¬ p.InRecord q ∧ Float64Access.Outside buffers q

def Action.ReadSafe (action : Action) (readers : ReadBank) : Prop :=
  ∀ q, readers.Region q → action.Outside q

variable {readers : ReadBank}

theorem ReadBank.Frame.refl (readers : ReadBank) (heap : Heap) : readers.Frame heap heap :=
  fun _ _ => rfl

theorem ReadBank.Frame.trans (first : readers.Frame before middle)
    (second : readers.Frame middle after) : readers.Frame before after :=
  fun q member => (second q member).trans (first q member)

theorem ReadBank.Stored.framed (stored : readers.Stored before) (frame : readers.Frame before after) :
    readers.Stored after := by
  intro request member
  apply (stored request member).framed
  intro q inside
  exact frame q ⟨request, member, inside⟩

/-- Ordinary category reads cannot alias an atomic reservation flag. This
follows from the original heap, without a new private-buffer assumption. -/
theorem ReadBank.Stored.not_flag {objects : Objects} {owners : SlotOwners.State objects.capacity}
    (stored : readers.Stored heap) (represented : SlotOwners.Represents objects.flagsBlock heap owners)
    (inside : readers.Region q) (slot : Fin objects.capacity) :
    q ≠ AtomicSlots.address objects.flagsBlock slot := by
  obtain ⟨request, member, region⟩ := inside
  have readable := (stored request member).load_ne_none region
  intro same
  subst q
  exact readable (by simp [load, represented slot, CAtomicBoolean.cell])

theorem Result.inputs_framed
    (result : Result objects retained owners p buffers heap after kind state action)
    (guarded : readers.Guarded objects retained p buffers)
    (safe : action.ReadSafe readers) : readers.Frame heap after := by
  intro q inside
  obtain ⟨guardedCell, outside, bankOutside⟩ := guarded q inside
  exact result.frame q guardedCell outside bankOutside (safe q inside)

end Rumoca.FMI3.InitializationProtocol
end
