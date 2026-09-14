import RumocaFMI3.Float64Buffers

noncomputable section
namespace Rumoca.FMI3.Float64Access
open CMemory Float64Buffers

structure Instance (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (state : ModelExchange.State) (time : Binary64.Value) : Prop where
  kind : load heap (p.member "kind") = some (.integer kind.code)
  mode : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩
  state : heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite state.x)⟩
  time : load heap (p.member "time") = some (.finite time)

variable {kind : Kind} {mode : Mode} {state afterState : ModelExchange.State} {time : Binary64.Value}

theorem Instance.mode_loaded (stored : Instance heap p kind mode state time) :
    load heap (p.member "mode") = some (.integer mode.code) := by
  cases mode <;> simp [load, stored.mode, convert, Mode.code]

theorem Instance.represented (stored : Instance heap p kind mode state time) :
    StateProofs.Represents heap p state := by
  simp [StateProofs.Represents, load, stored.state, convert, Value.finite]

def Outside (buffers : Layout) (q : Address) : Prop :=
  (∀ i < buffers.capacity.toNat, q ≠ buffers.references.index i) ∧
  (∀ i < buffers.capacity.toNat, q ≠ buffers.values.index i)

theorem instance_outside (separate : buffers.Separate p) (sameBlock : q.block = p.block) :
    Outside buffers q := by
  constructor
  · intro i _
    apply different_blocks
    simpa only [Address.index, sameBlock] using separate.references.symm
  · intro i _
    apply different_blocks
    simpa only [Address.index, sameBlock] using separate.values.symm

theorem Instance.changed (stored : Instance heap p kind mode state time)
    (separate : buffers.Separate p)
    (frame : ∀ q, q ≠ StateProofs.stateAddress p → Outside buffers q → after q = heap q)
    (cell : after (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite afterState.x)⟩) :
    Instance after p kind mode afterState time := by
  have fields : ∀ name, after (p.member name) = heap (p.member name) := fun name =>
    frame _ (Ne.symm (HistoryBodies.state_ne_field p name)) (instance_outside separate rfl)
  exact ⟨by simpa only [load, fields] using stored.kind,
    (fields "mode").trans stored.mode, cell, by simpa only [load, fields] using stored.time⟩

inductive Request where
  | get (shape : Tensor.Shape) (references : Nat → UInt32)
  | set {shape : Tensor.Shape} (values : TensorView.Values shape)

def Request.shape : Request → Tensor.Shape
  | .get shape _ => shape
  | .set (shape := shape) _ => shape

def Request.references : Request → Nat → UInt32
  | .get _ references => references
  | .set _ => fun _ => 1

def Request.isWrite : Request → Bool
  | .get _ _ => false
  | .set _ => true

def Request.Fits (request : Request) (buffers : Layout) : Prop :=
  request.shape.volume ≤ buffers.capacity.toNat

def Request.Allowed (request : Request) (kind : Kind) (mode : Mode) : Prop :=
  match request with
  | .get shape references => Reference.Allowed .get kind mode ∧ ∀ i < shape.volume, (references i).toNat ≤ 2
  | .set _ => Reference.Allowed .setStart kind mode

/-- Before entering initialization, only state start-value queries are used.
Equation and time queries belong to the initialized equation environment. -/
def Request.StartQuery (request : Request) : Prop :=
  match request with
  | .get shape references => ∀ i < shape.volume, (references i).toNat = 1
  | .set _ => True

def Request.prepare (request : Request) (heap : Heap) (buffers : Layout) : Heap :=
  let ready := prepareReferences heap buffers request.shape request.references
  match request with
  | .get _ _ => ready
  | .set values => TensorView.written ready buffers.values values request.shape.volume

/-- Actual typed host stores are part of the history's execution relation. -/
def Request.hostRun (request : Request) (heap : Heap) (buffers : Layout) : Option Heap := do
  let ready ← ArrayStore.run heap buffers.references
    (referenceValues request.shape request.references) request.shape.volume
  match request with
  | .get _ _ => some ready
  | .set values => ArrayStore.run ready buffers.values (finiteValues values) request.shape.volume

theorem Request.prepare_frame (request : Request) (heap : Heap) (buffers : Layout)
    (fits : request.Fits buffers) (outside : Outside buffers q) :
    request.prepare heap buffers q = heap q := by
  cases request with
  | get shape references => exact references_frame _ _ _ _ _ (fun i hi => outside.1 i (Nat.lt_of_lt_of_le hi fits))
  | set values =>
    exact (TensorView.written_frame _ _ _ _ _ (fun i hi => outside.2 i (by exact Nat.lt_of_lt_of_le hi fits))).trans
      (references_frame _ _ _ _ _ (fun i hi => outside.1 i (by exact Nat.lt_of_lt_of_le hi fits)))

theorem Request.prepare_correct (request : Request) (stored : Stored heap buffers)
    (fits : request.Fits buffers) :
    request.hostRun heap buffers = some (request.prepare heap buffers) ∧
    Stored (request.prepare heap buffers) buffers ∧
    CStorage.Preserves heap (request.prepare heap buffers) ∧
    CReadOnly.Preserves heap (request.prepare heap buffers) := by
  have run := references_run stored request.shape request.references fits
  have frames := references_preserve stored request.shape request.references fits
  have refsStored := stored.preserved frames.1
  cases request with
  | get shape references => exact ⟨by simpa [Request.hostRun, Request.prepare] using run,
      refsStored, frames⟩
  | set values =>
    have writable : TensorView.Writable
        (prepareReferences heap buffers (Request.set values).shape (Request.set values).references)
        buffers.values (Request.set values).shape.volume := by
      intro i hi
      exact refsStored.values i (by simpa using Nat.lt_of_lt_of_le hi fits)
    have written := values_run _ buffers.values values writable
    have lastFrames := values_preserve _ buffers.values values writable
    exact ⟨by simp only [Request.hostRun, run]; exact written,
      refsStored.preserved lastFrames.1, frames.1.trans lastFrames.1, frames.2.trans lastFrames.2⟩

theorem Request.prepared_instance (request : Request) (stored : Instance heap p kind mode state time)
    (fits : request.Fits buffers) (separate : buffers.Separate p) :
    Instance (request.prepare heap buffers) p kind mode state time := by
  apply stored.changed separate (fun q _ outside => request.prepare_frame heap buffers fits outside)
  exact (request.prepare_frame heap buffers fits
    (instance_outside (q := StateProofs.stateAddress p) separate rfl)).trans stored.state

theorem Request.prepared_references (request : Request) (heap : Heap) (buffers : Layout)
    (separate : buffers.Separate p) :
    Float64Calls.References (request.prepare heap buffers) (some buffers.references)
      request.shape.volume request.references := by
  have readable := references_read heap buffers request.shape request.references
  cases request with
  | get _ _ => exact readable
  | set values =>
    exact Float64Calls.references_written _ _ _ values _ _ readable
      (fun base equal i _ j _ => by
        cases Option.some.inj equal
        exact different_blocks _ _ separate.eachOther)

def Request.next (request : Request) (state : ModelExchange.State) : ModelExchange.State :=
  match request with
  | .get _ _ => state
  | .set (shape := shape) values => if nonempty : 0 < shape.volume then
      ⟨values[shape.volume - 1]⟩ else state

def Request.call (request : Request) (p : Address) (buffers : Layout) : String × List Value :=
  let count := UInt64.ofNat request.shape.volume
  ((Float64Calls.signature request.isWrite).name,
    Float64Calls.arguments (some p) (some buffers.references) (some buffers.values) count count)

def Request.after (model : Solve.FMI3Model source) (request : Request) (heap : Heap)
    (p : Address) (buffers : Layout) (state : ModelExchange.State) (time : Binary64.Value) : Heap :=
  let ready := request.prepare heap buffers
  match request with
  | .get shape references => TensorView.written ready buffers.values
      (Float64Calls.outputValues model state time shape (fun i => Float64Calls.selectReference (references i))) shape.volume
  | .set values => Float64Set.assigned ready p values request.shape.volume

end Rumoca.FMI3.Float64Access
end

noncomputable section
namespace Rumoca.FMI3.Float64Access
open CMemory Float64Buffers

theorem Request.volume (request : Request) (fits : request.Fits buffers) :
    request.shape.volume = (UInt64.ofNat request.shape.volume).toNat :=
  (UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt fits buffers.capacity.toNat_lt_size)).symm

theorem Request.after_frame (model : Solve.FMI3Model source) (request : Request)
    (heap : Heap) (p : Address) (buffers : Layout) (state : ModelExchange.State) (time : Binary64.Value)
    (fits : request.Fits buffers) (q : Address) (notState : q ≠ StateProofs.stateAddress p)
    (outside : Outside buffers q) :
    request.after model heap p buffers state time q = heap q := by
  cases request with
  | get shape references =>
    exact (TensorView.written_frame _ _ _ _ q
      (fun i hi => outside.2 i (Nat.lt_of_lt_of_le hi fits))).trans
      (Request.prepare_frame _ heap buffers fits outside)
  | set values =>
    exact (Float64Set.assigned_frame _ _ values _ q notState).trans
      (Request.prepare_frame _ heap buffers fits outside)

theorem assigned_final (heap : Heap) (p : Address) (values : TensorView.Values shape)
    (nonempty : 0 < shape.volume) :
    Float64Set.assigned heap p values shape.volume =
      StateProofs.written heap (StateProofs.stateAddress p) (Binary64.toBits values[shape.volume - 1]).val := by
  have count : shape.volume = (shape.volume - 1) + 1 := by omega
  conv => lhs; arg 4; rw [count]
  rw [Float64Set.assigned, dif_pos (by omega)]

theorem assigned_correct (heap : Heap) (p : Address) (values : TensorView.Values shape)
    (state : ModelExchange.State)
    (cell : heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite state.x)⟩) :
    CStorage.Preserves heap (Float64Set.assigned heap p values shape.volume) ∧
    CReadOnly.Preserves heap (Float64Set.assigned heap p values shape.volume) ∧
    Float64Set.assigned heap p values shape.volume (StateProofs.stateAddress p) =
      some ⟨.float64, true, some (.finite ((Request.set values).next state).x)⟩ := by
  by_cases nonempty : 0 < shape.volume
  · rw [assigned_final heap p values nonempty]
    have step := store_float64 heap (StateProofs.stateAddress p) (some (.finite state.x))
      (Binary64.toBits values[shape.volume - 1]).val cell
    refine ⟨CStorage.store_preserves step, CReadOnly.store_preserves step, ?_⟩
    simp [StateProofs.written, Request.next, nonempty, Value.finite]
  · have empty : shape.volume = 0 := by omega
    simpa only [empty, Float64Set.assigned, Request.next, nonempty, dite_false] using
      And.intro (CStorage.Preserves.refl heap) (And.intro (CReadOnly.Preserves.refl heap) cell)

def Request.Observes (request : Request) (model : Solve.FMI3Model source)
    (state : ModelExchange.State) (time : Binary64.Value) (heap : Heap) (buffers : Layout) : Prop :=
  match request with
  | .get shape references => ∀ i < shape.volume, load heap (buffers.values.index i) =
      some (.finite ((Float64Calls.selectReference (references i)).value model state time))
  | .set _ => True

/-- Accepted batched accesses derive both typed host transfers and every
complete target-call behavior from original storage. -/
theorem step [CInterface] (program : CCalls.Events.Program E)
    (get : ∀ heap, Float64Calls.QuietExecutionContract model program heap)
    (set : ∀ heap, Float64Set.QuietExecutionContract program heap)
    (request : Request) (stored : Instance heap p kind mode state time)
    (buffersStored : Stored heap buffers) (fits : request.Fits buffers)
    (separate : buffers.Separate p) (allowed : request.Allowed kind mode) :
    let ready := request.prepare heap buffers
    let after := request.after model heap p buffers state time
    request.hostRun heap buffers = some ready ∧
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (request.call p buffers).1 (request.call p buffers).2 ready .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, after⟩) ∧
    Instance after p kind mode (request.next state) time ∧ Stored after buffers ∧
    request.Observes model state time after buffers ∧
    CStorage.Preserves heap after ∧ CReadOnly.Preserves heap after ∧
    (∀ q, q ≠ StateProofs.stateAddress p → Outside buffers q → after q = heap q) := by
  obtain ⟨hostRun, preparedBuffers, bufferFrame, readonlyFrame⟩ := request.prepare_correct buffersStored fits
  have prepared := request.prepared_instance stored fits separate
  have readable := request.prepared_references heap buffers separate
  have count := request.volume fits
  have stateSeparate : ∀ i < request.shape.volume,
      StateProofs.stateAddress p ≠ buffers.values.index i := fun _ _ =>
    different_blocks _ _ separate.values.symm
  have result :
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (request.call p buffers).1 (request.call p buffers).2
          (request.prepare heap buffers) .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, request.after model heap p buffers state time⟩) ∧
      CStorage.Preserves (request.prepare heap buffers) (request.after model heap p buffers state time) ∧
      CReadOnly.Preserves (request.prepare heap buffers) (request.after model heap p buffers state time) ∧
      request.after model heap p buffers state time (StateProofs.stateAddress p) =
        some ⟨.float64, true, some (.finite (request.next state).x)⟩ ∧
      request.Observes model state time (request.after model heap p buffers state time) buffers := by
    cases request with
    | get shape references =>
      have writable : TensorView.Writable _ buffers.values shape.volume :=
        fun i hi => preparedBuffers.values i (Nat.lt_of_lt_of_le hi fits)
      have called := (get _).get p buffers.references buffers.values (UInt64.ofNat shape.volume)
        shape references kind mode state time count prepared.kind prepared.mode_loaded allowed.1 readable allowed.2
        writable (fun _ _ _ _ => different_blocks _ _ separate.eachOther)
        prepared.represented stateSeparate prepared.time (fun _ _ => different_blocks _ _ separate.values.symm)
      have frames := values_preserve _ buffers.values
        (Float64Calls.outputValues model state time shape (fun i => Float64Calls.selectReference (references i))) writable
      refine ⟨called, frames.1, frames.2, ?_, ?_⟩
      · exact (TensorView.written_frame _ _ _ _ _ stateSeparate).trans prepared.state
      · intro i hi
        have loaded := TensorView.written_reads ((Request.get shape references).prepare heap buffers) buffers.values
          (Float64Calls.outputValues model state time shape (fun i => Float64Calls.selectReference (references i))) ⟨i, hi⟩
        change load ((Request.get shape references).after model heap p buffers state time)
          (buffers.values.index i) = some (.finite
            (Float64Calls.outputValues model state time shape (fun j => Float64Calls.selectReference (references j)))[i]) at loaded
        simpa only [Float64Calls.outputValues_at] using loaded
    | set values =>
      have assigned := assigned_correct _ p values state prepared.state
      refine ⟨?_, assigned.1, assigned.2.1, assigned.2.2, trivial⟩
      by_cases nonempty : 0 < (Request.set values).shape.volume
      · exact (set _).set p buffers.references buffers.values _ _ values _ kind mode _ count nonempty
          prepared.kind prepared.mode_loaded allowed readable (fun _ _ => rfl)
          (TensorView.written_reads _ _ values) prepared.state stateSeparate
      · have empty : (Request.set values).shape.volume = 0 := by omega
        have called := (set ((Request.set values).prepare heap buffers)).empty p
          (some buffers.references) (some buffers.values) kind mode prepared.kind prepared.mode_loaded
        simpa only [Request.call, Request.isWrite, Request.after, empty, Float64Set.assigned] using called
  obtain ⟨called, storedFrame, readonly, cell, observes⟩ := result
  have frame := request.after_frame model heap p buffers state time fits
  exact ⟨hostRun, called, stored.changed separate frame cell,
    buffersStored.preserved (bufferFrame.trans storedFrame), observes,
    bufferFrame.trans storedFrame, readonlyFrame.trans readonly, frame⟩

end Rumoca.FMI3.Float64Access
end
