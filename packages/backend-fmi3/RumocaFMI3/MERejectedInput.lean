import RumocaFMI3.MEFailureContracts
import RumocaFMI3.MEFailureMemory

noncomputable section
namespace Rumoca.FMI3.MEFailure
open CTree CMemory CBody StaticFactory

/-- An optional importer write to the reusable float buffer retains raw IEEE
bits. In particular the caller can supply NaN or infinity for a rejected setter. -/
def prepare (input : Option (BitVec 64)) (heap : Heap) (buffer : Address) : Heap :=
  match input with | none => heap | some bits => StateProofs.written heap buffer bits

def Prepares (input : Option (BitVec 64)) (heap ready : Heap) (buffer : Address) : Prop :=
  match input with | none => ready = heap | some bits => store heap buffer (.float64 bits) = some ready

theorem Prepares.unique {input : Option (BitVec 64)}
    (first : Prepares input heap ready buffer) (second : Prepares input heap other buffer) : ready = other := by
  cases input <;> simp_all [Prepares]

theorem prepare_frame (input : Option (BitVec 64)) (heap : Heap) (buffer q : Address)
    (different : q ≠ buffer) : prepare input heap buffer q = heap q := by
  cases input with
  | none => rfl
  | some bits => exact StateProofs.written_frame heap buffer q bits different

theorem prepare_correct (input : Option (BitVec 64))
    (stored : MENumericalHistory.Stored heap p clock reference addresses buffer)
    (reset : Reset.Storage heap p) :
    Prepares input heap (prepare input heap buffer) buffer ∧
    MENumericalHistory.Stored (prepare input heap buffer) p clock reference addresses buffer ∧
    Reset.Storage (prepare input heap buffer) p ∧
    CReadOnly.Preserves heap (prepare input heap buffer) ∧
    CAtomicBoolean.Preserves heap (prepare input heap buffer) := by
  cases input with
  | none => exact ⟨rfl, stored, reset, .refl _, .refl _⟩
  | some bits =>
    obtain ⟨old, cell⟩ := stored.bufferCell
    have written := store_float64 heap buffer old bits cell
    have next : MENumericalHistory.Stored (StateProofs.written heap buffer bits) p clock reference addresses buffer := by
      apply stored.changed reference.state
      · intro q _ other
        exact StateProofs.written_frame heap buffer q bits other
      · exact (StateProofs.written_frame heap buffer _ bits stored.state_ne_buffer).trans stored.stateCell
      · exact ⟨some (.float64 bits), by simp [StateProofs.written]⟩
    refine ⟨written, next, ?_, CReadOnly.store_preserves written,
      CAtomicBoolean.replace_nonatomic cell (by intro h; cases h) _⟩
    exact reset.record_preserved (fun q inside => StateProofs.written_frame heap buffer q bits
      (fun same => stored.bufferOutside (by simpa only [same] using inside.1)))

/-- Rejection selection is expressed using the reference protocol, raw caller
arguments and current clock. It contains no target execution or future heap. -/
def Request.Selected (request : Request) (input : Option (BitVec 64))
    (buffer : Address) (clock : Time.Clock) (reference : MENumericalHistory.ReferenceState) : Prop :=
  match request with
  | .state write .lifecycle _ _ => ¬ Reference.Allowed (StateCalls.Entry.command write) .me reference.control.mode
  | .state write .access pointer count => Reference.Allowed (StateCalls.Entry.command write) .me reference.control.mode ∧
      (count.toNat ≠ 1 ∨ pointer = none)
  | .state write .nonfinite pointer count => write = true ∧
      Reference.Allowed (StateCalls.Entry.command write) .me reference.control.mode ∧ count = 1 ∧
      pointer = some buffer ∧ ∃ bits, input = some bits ∧ (Value.float64 bits).isFinite = some false
  | .derivative access pointer count => DerivativeCalls.FailureCondition access .me reference.control.mode pointer count
  | .time reason bits window minimum => TimeCalls.FailureCondition reason .me reference.control.mode window bits ∧
      (reason = .window → window = reference.control.history.window ∧ minimum = clock.minimum)
  | .entry transition => ¬ Reference.Allowed transition.command .me reference.control.mode
  | .completed reason event terminate _ => CompletedCalls.FailureCondition reason .me reference.control.mode event terminate
  | .discrete reason pointers => DiscreteCalls.FailureCondition reason .me reference.control.mode pointers

theorem Request.Selected.condition {request : Request}
    (selected : request.Selected input buffer clock reference)
    (stored : MENumericalHistory.Stored (prepare input heap buffer) p clock reference addresses buffer) :
    request.Condition (prepare input heap buffer) p .me reference.control.mode := by
  cases request with
  | state write reason pointer count =>
    cases reason with
    | lifecycle | access => exact selected
    | nonfinite =>
      obtain ⟨write, allowed, count, pointer, bits, input, invalid⟩ := selected
      refine ⟨write, allowed, count, buffer, bits, pointer, ?_, invalid⟩
      simp [input, prepare, StateProofs.written, load, convert]
  | derivative _ _ _ | entry _ | completed _ _ _ _ | discrete _ _ => exact selected
  | time reason bits window minimum =>
    refine ⟨selected.1, ?_⟩
    intro failure
    obtain ⟨rfl, rfl⟩ := selected.2 failure
    exact ⟨stored.control.history.minimum, by
      simp [load, stored.control.clockStored.minimum, HistoryProofs.cell, convert, Value.finite],
      stored.control.stopDefined, stored.control.stopValue⟩

end Rumoca.FMI3.MEFailure
end
