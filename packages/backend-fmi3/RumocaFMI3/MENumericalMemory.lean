import RumocaFMI3.MEHistory

noncomputable section
namespace Rumoca.FMI3.MENumericalHistory
open CTree CMemory

/-- An importer trial state is separate from the immutable source initial
value. The control protocol and the trial state evolve independently. -/
structure ReferenceState where
  control : MEHistory.ReferenceState
  state : ModelExchange.State

/-- One reusable float buffer and the existing control output bank. Writable
state storage survives queries and control transitions. The float buffer is
outside instance storage and separate from the control output bank. -/
structure Stored (heap : Heap) (p : Address) (clock : Time.Clock)
    (reference : ReferenceState) (addresses : String → Address) (buffer : Address) : Prop where
  control : MEHistory.Stored heap p clock reference.control reference.state addresses
  stateCell : heap (StateProofs.stateAddress p) =
    some ⟨.float64, true, some (.finite reference.state.x)⟩
  bufferCell : ∃ old, heap buffer = some ⟨.float64, true, old⟩
  bufferOutside : buffer.block ≠ p.block
  bufferSeparate : ∀ name ∈ DiscreteCalls.names, buffer ≠ addresses name

theorem Stored.field_ne_buffer (stored : Stored heap p clock reference addresses buffer)
    (name : String) : p.member name ≠ buffer := by
  intro same
  exact stored.bufferOutside (by simpa using (congrArg Address.block same).symm)

theorem Stored.state_ne_buffer (stored : Stored heap p clock reference addresses buffer) :
    StateProofs.stateAddress p ≠ buffer := by
  intro same
  exact stored.bufferOutside (by simpa [StateProofs.stateAddress] using (congrArg Address.block same).symm)

/-- Numerical access and caller buffer preparation change only the current
state and float buffer. Every control/cache/output premise is retained. -/
theorem Stored.changed (stored : Stored heap p clock reference addresses buffer)
    (state : ModelExchange.State)
    (frame : ∀ q, q ≠ StateProofs.stateAddress p → q ≠ buffer → after q = heap q)
    (stateCell : after (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite state.x)⟩)
    (bufferCell : ∃ old, after buffer = some ⟨.float64, true, old⟩) :
    Stored after p clock { reference with state := state } addresses buffer := by
  have fields : ∀ name, after (p.member name) = heap (p.member name) := fun name =>
    frame _ (Ne.symm (HistoryBodies.state_ne_field p name)) (stored.field_ne_buffer name)
  refine ⟨?_, stateCell, bufferCell, stored.bufferOutside, stored.bufferSeparate⟩
  constructor
  · simpa only [load, fields] using stored.control.kind
  · simpa only [fields] using stored.control.mode
  · exact ⟨(fields "time").trans stored.control.clockStored.time,
      (fields "timeMin").trans stored.control.clockStored.minimum,
      (fields "eventTime").trans stored.control.clockStored.eventTime,
      (fields "lastCompleted").trans stored.control.clockStored.lastCompleted⟩
  · exact stored.control.history
  · simp [StateProofs.Represents, load, stateCell, convert, Value.finite]
  · simpa only [load, fields] using stored.control.stopDefined
  · intro stop bound
    simpa only [load, fields] using stored.control.stopValue stop bound
  · apply stored.control.buffers.transport
    intro layout member
    have named : layout.1 ∈ DiscreteCalls.names := List.mem_map.mpr ⟨layout, member, rfl⟩
    apply frame
    · intro same
      exact stored.control.outside layout.1 named
        (by simpa [StateProofs.stateAddress] using congrArg Address.block same)
    · exact Ne.symm (stored.bufferSeparate layout.1 named)
  · exact stored.control.outside

theorem Stored.write_buffer (stored : Stored heap p clock reference addresses buffer)
    (value : Binary64.Value) :
    Stored (StateProofs.written heap buffer (Binary64.toBits value).val)
      p clock reference addresses buffer := by
  apply stored.changed reference.state
  · intro q _ other
    exact StateProofs.written_frame heap buffer q _ other
  · simpa only [StateProofs.written_frame heap buffer _ _ stored.state_ne_buffer] using stored.stateCell
  · exact ⟨some (.finite value), by simp [StateProofs.written, Value.finite]⟩

/-- The importer supplies a trial value through an actual typed caller write;
the later setter does not assume an already populated future heap. -/
theorem Stored.prepare_buffer (stored : Stored heap p clock reference addresses buffer)
    (value : Binary64.Value) :
    store heap buffer (.finite value) =
      some (StateProofs.written heap buffer (Binary64.toBits value).val) ∧
    Stored (StateProofs.written heap buffer (Binary64.toBits value).val)
      p clock reference addresses buffer ∧
    CReadOnly.Preserves heap (StateProofs.written heap buffer (Binary64.toBits value).val) := by
  obtain ⟨old, cell⟩ := stored.bufferCell
  have written := store_float64 heap buffer old (Binary64.toBits value).val cell
  exact ⟨written, stored.write_buffer value, CReadOnly.store_preserves written⟩

theorem Stored.write_state (stored : Stored heap p clock reference addresses buffer)
    (value : Binary64.Value) :
    Stored (StateProofs.written heap (StateProofs.stateAddress p) (Binary64.toBits value).val)
      p clock { reference with state := ModelExchange.setContinuousState reference.state value }
      addresses buffer := by
  apply stored.changed (ModelExchange.setContinuousState reference.state value)
  · intro q other _
    exact StateProofs.written_frame heap (StateProofs.stateAddress p) q _ other
  · simp [StateProofs.written, ModelExchange.setContinuousState, Value.finite]
  · obtain ⟨old, cell⟩ := stored.bufferCell
    exact ⟨old, (StateProofs.written_frame heap (StateProofs.stateAddress p) buffer _
      (Ne.symm stored.state_ne_buffer)).trans cell⟩

theorem Stored.control_frame (stored : Stored heap p clock reference addresses buffer) :
    MEHistory.Outside p addresses (StateProofs.stateAddress p) ∧
    MEHistory.Outside p addresses buffer := by
  constructor
  · refine ⟨HistoryBodies.state_ne_field p "time", HistoryBodies.state_ne_field p "mode",
      HistoryBodies.state_ne_field p "eventTime", HistoryBodies.state_ne_field p "timeMin",
      HistoryBodies.state_ne_field p "lastCompleted", ?_⟩
    intro name member same
    exact stored.control.outside name member
      (by simpa [StateProofs.stateAddress] using (congrArg Address.block same).symm)
  · exact ⟨Ne.symm (stored.field_ne_buffer "time"), Ne.symm (stored.field_ne_buffer "mode"),
      Ne.symm (stored.field_ne_buffer "eventTime"), Ne.symm (stored.field_ne_buffer "timeMin"),
      Ne.symm (stored.field_ne_buffer "lastCompleted"), stored.bufferSeparate⟩

end Rumoca.FMI3.MENumericalHistory
end
