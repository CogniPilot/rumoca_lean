import RumocaFMI3.Float64Rejection
import RumocaFMI3.Float64RawBuffers
import RumocaFMI3.Float64Access

noncomputable section
namespace Rumoca.FMI3.Float64Rejection
open CMemory Float64Buffers

def inputValues (count : Nat) (references : Nat → UInt32) : Fin count → Value :=
  fun i => .integer (references i.val).toNat

def inputHeap (heap : Heap) (base : Address) (count : Nat) (references : Nat → UInt32) : Heap :=
  ArrayStore.written heap base (.unsigned 32) (inputValues count references) count

/-- Only guards that inspect entries require caller transfers. Lifecycle and
array-shape failures retain no readable or writable array premise. -/
def Request.TransferStorage (request : Request) (heap : Heap) : Prop :=
  match request with
  | .get .reference (some input) _ n _ _ => ArrayStore.Writable heap input (.unsigned 32) n.toNat
  | .get .reference none _ _ _ _ => False
  | .set .entry (some input) (some buffer) n _ _ _ =>
      ArrayStore.Writable heap input (.unsigned 32) n.toNat ∧ TensorView.Writable heap buffer n.toNat ∧
      input.block ≠ buffer.block
  | .set .entry _ _ _ _ _ _ => False
  | _ => True

def Request.prepare (request : Request) (heap : Heap) : Heap :=
  match request with
  | .get .reference (some input) _ n _ references => inputHeap heap input n.toNat references
  | .set .entry (some input) (some buffer) n _ references bits =>
      prepareRawValues (inputHeap heap input n.toNat references) buffer n.toNat bits
  | _ => heap

def Request.hostRun (request : Request) (heap : Heap) : Option Heap :=
  match request with
  | .get .reference (some input) _ n _ references =>
      ArrayStore.run heap input (inputValues n.toNat references) n.toNat
  | .set .entry (some input) (some buffer) n _ references bits => do
      let ready ← ArrayStore.run heap input (inputValues n.toNat references) n.toNat
      ArrayStore.run ready buffer (rawValues n.toNat bits) n.toNat
  | _ => some heap

def Request.Outside (request : Request) (q : Address) : Prop :=
  match request with
  | .get .reference (some input) _ n _ _ => ∀ i < n.toNat, q ≠ input.index i
  | .set .entry (some input) (some buffer) n _ _ _ =>
      (∀ i < n.toNat, q ≠ input.index i) ∧ (∀ i < n.toNat, q ≠ buffer.index i)
  | _ => True

theorem input_run (heap : Heap) (input : Address) (count : Nat) (references : Nat → UInt32)
    (stored : ArrayStore.Writable heap input (.unsigned 32) count) :
    ArrayStore.run heap input (inputValues count references) count = some (inputHeap heap input count references) :=
  ArrayStore.run_written _ _ _ _ _ (by omega) stored (by decide) (fun i => reference_converts (references i.val))

theorem input_read (heap : Heap) (input : Address) (count : Nat) (references : Nat → UInt32) :
    Float64Calls.References (inputHeap heap input count references) (some input) count references := by
  intro i hi
  exact ⟨input, rfl, ArrayStore.written_reads heap input (.unsigned 32) (inputValues count references)
    (by decide) (fun j => reference_converts (references j.val)) ⟨i, hi⟩⟩

theorem Request.prepare_frame (request : Request) (heap : Heap) (q : Address) (outside : request.Outside q) :
    request.prepare heap q = heap q := by
  cases request with
  | get reason input buffer n m references =>
    cases reason with
    | arrays => rfl
    | reference => cases input with
      | none => rfl
      | some input => exact ArrayStore.frame _ _ _ _ _ q (fun i => outside i.val i.isLt)
  | set reason input buffer n m references bits =>
    cases reason with
    | lifecycle | arrays => rfl
    | entry => cases input with
      | none => rfl
      | some input => cases buffer with
        | none => rfl
        | some buffer =>
          exact (raw_values_frame _ _ _ _ _ outside.2).trans
            (ArrayStore.frame _ _ _ _ _ q (fun i => outside.1 i.val i.isLt))

/-- Every input snapshot comes from actual typed caller stores. The universal
result includes NaNs/infinities and does not assume successful FMI execution. -/
theorem Request.prepare_correct (request : Request) (heap : Heap) (stored : request.TransferStorage heap) :
    request.hostRun heap = some (request.prepare heap) ∧ request.Readable (request.prepare heap) ∧
    CStorage.Preserves heap (request.prepare heap) ∧ CReadOnly.Preserves heap (request.prepare heap) ∧
    CAtomicBoolean.Preserves heap (request.prepare heap) := by
  cases request with
  | get reason input buffer n m references =>
    cases reason with
    | arrays =>
      refine ⟨rfl, ?_, .refl _, .refl _, .refl _⟩
      intro h
      cases h
    | reference => cases input with
      | none => exact False.elim stored
      | some input =>
        have run := input_run heap input n.toNat references stored
        have preserved := ArrayStore.run_preserves run
        exact ⟨run, fun _ => input_read heap input n.toNat references, preserved.1, preserved.2,
          CStoreInvariant.array_run CAtomicBoolean.ordinary_stable (fun a b => a.trans b) run⟩
  | set reason input buffer n m references bits =>
    cases reason with
    | lifecycle | arrays =>
      refine ⟨rfl, ?_, .refl _, .refl _, .refl _⟩
      intro h
      cases h
    | entry => cases input with
      | none => exact False.elim stored
      | some input => cases buffer with
        | none => exact False.elim stored
        | some buffer =>
          obtain ⟨referencesStored, valuesStored, separate⟩ := stored
          have first := input_run heap input n.toNat references referencesStored
          have firstFrame := ArrayStore.run_preserves first
          have writable : TensorView.Writable (inputHeap heap input n.toNat references) buffer n.toNat := by
            intro i hi
            obtain ⟨old, cell⟩ := valuesStored i hi
            exact firstFrame.1.cell cell
          have second := raw_values_run _ buffer n.toNat bits writable
          have secondFrame := raw_values_preserve _ buffer n.toNat bits writable
          refine ⟨by simp only [Request.hostRun, first]; exact second,
            ?_, firstFrame.1.trans secondFrame.1, firstFrame.2.trans secondFrame.2.1,
            (CStoreInvariant.array_run CAtomicBoolean.ordinary_stable (fun a b => a.trans b) first).trans secondFrame.2.2⟩
          intro _
          constructor
          · intro i hi
            refine ⟨input, rfl, ?_⟩
            have unchanged := raw_values_frame (inputHeap heap input n.toNat references) buffer n.toNat bits
              (input.index i) (fun j _ => different_blocks _ _ separate)
            have readable := ArrayStore.written_reads heap input (.unsigned 32) (inputValues n.toNat references)
              (by decide) (fun j => reference_converts (references j.val)) ⟨i, hi⟩
            change load (prepareRawValues (inputHeap heap input n.toNat references) buffer n.toNat bits)
              (input.index i) = some (.integer (references i).toNat)
            unfold load
            rw [unchanged]
            exact readable
          · intro i hi _
            exact ⟨buffer, rfl, raw_values_read _ buffer n.toNat bits i hi⟩

theorem Request.prepared_instance (request : Request)
    (stored : Float64Access.Instance heap p kind mode state time)
    (separate : ∀ q, p.InRecord q → request.Outside q) :
    Float64Access.Instance (request.prepare heap) p kind mode state time := by
  have fields (name : String) := request.prepare_frame heap (p.member name)
    (separate _ (p.member_in_record name))
  have stateCell := request.prepare_frame heap (StateProofs.stateAddress p)
    (separate _ ((p.member_in_record "model").member "x"))
  exact ⟨by simpa only [load, fields] using stored.kind,
    (fields "mode").trans stored.mode, stateCell.trans stored.state,
    by simpa only [load, fields] using stored.time⟩

end Rumoca.FMI3.Float64Rejection
end
