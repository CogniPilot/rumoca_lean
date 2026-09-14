import RumocaFMI3.MENumericalHistory
import RumocaFMI3.MELifecycle

noncomputable section
namespace Rumoca.FMI3.MENumericalHistory
open CTree CMemory

/-- Caller-owned storage can be provided before factory execution. No
instance values or post-creation contents occur in this prerequisite. -/
structure CallerStorage (heap : Heap) (p : Address) (addresses : String → Address)
    (buffer : Address) : Prop where
  controls : MEHistory.Buffers heap addresses
  outside : MEHistory.Buffers.Outside p addresses
  bufferCell : ∃ old, heap buffer = some ⟨.float64, true, old⟩
  bufferOutside : buffer.block ≠ p.block
  bufferSeparate : ∀ name ∈ DiscreteCalls.names, buffer ≠ addresses name

theorem CallerStorage.storage_preserved (stored : CallerStorage before p addresses buffer)
    (preserved : CStorage.Preserves before after) : CallerStorage after p addresses buffer := by
  obtain ⟨old, found⟩ := stored.bufferCell
  exact ⟨stored.controls.storage_preserved preserved, stored.outside,
    preserved.cell found, stored.bufferOutside, stored.bufferSeparate⟩

theorem CallerStorage.at_index (stored : CallerStorage heap p addresses buffer) (slot : Nat) :
    CallerStorage heap (p.index slot) addresses buffer :=
  ⟨stored.controls, stored.outside, stored.bufferCell, stored.bufferOutside, stored.bufferSeparate⟩

theorem Stored.callers (stored : Stored heap p clock reference addresses buffer) :
    CallerStorage heap p addresses buffer :=
  ⟨stored.control.buffers, stored.control.outside, stored.bufferCell, stored.bufferOutside, stored.bufferSeparate⟩

def ReferenceState.initial (args : Initialization.Arguments) (seed : Binary64.Value) : ReferenceState :=
  ⟨MEHistory.ReferenceState.initial args.start args.stopTime, ⟨seed⟩⟩

/-- Initialization establishes the complete mixed-history storage invariant,
including the original finite state cell and the first event-iteration duty. -/
theorem initialized_stored (heap : Heap) (p : Address) (args : Initialization.Arguments)
    (seed : Binary64.Value) (addresses : String → Address) (buffer : Address)
    (admissible : args.Admissible)
    (kind : load heap (p.member "kind") = some (.integer 0))
    (stateCell : heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite seed)⟩)
    (outputs : CallerStorage heap p addresses buffer) :
    Stored (InitializationCalls.exitedHeap heap p args .me) p (Time.Clock.initial args.start)
      (ReferenceState.initial args seed) addresses buffer := by
  have represented : StateProofs.Represents heap p ⟨seed⟩ := by
    simp [StateProofs.Represents, load, stateCell, convert, Value.finite]
  have control := MEHistory.initialized_stored heap p args ⟨seed⟩ addresses admissible kind
    represented outputs.controls outputs.outside
  have stateFrame := InitializationCalls.exited_frame heap p (StateProofs.stateAddress p) args .me
    (HistoryBodies.state_ne_field p "time") (HistoryBodies.state_ne_field p "timeMin")
    (HistoryBodies.state_ne_field p "eventTime") (HistoryBodies.state_ne_field p "lastCompleted")
    (HistoryBodies.state_ne_field p "stop") (HistoryBodies.state_ne_field p "stopDefined")
    (HistoryBodies.state_ne_field p "mode")
  have bufferField : ∀ name, buffer ≠ p.member name := by
    intro name same
    exact outputs.bufferOutside (by simpa using congrArg Address.block same)
  have bufferFrame := InitializationCalls.exited_frame heap p buffer args .me
    (bufferField "time") (bufferField "timeMin") (bufferField "eventTime") (bufferField "lastCompleted")
    (bufferField "stop") (bufferField "stopDefined") (bufferField "mode")
  obtain ⟨old, cell⟩ := outputs.bufferCell
  exact ⟨control, stateFrame.trans stateCell, ⟨old, bufferFrame.trans cell⟩,
    outputs.bufferOutside, outputs.bufferSeparate⟩

end Rumoca.FMI3.MENumericalHistory
end
