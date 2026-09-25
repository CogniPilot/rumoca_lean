import RumocaFMI3.Float64Atomic
import RumocaFMI3.Float64History
import RumocaFMI3.AbsentVariableRuntime
import RumocaFMI3.LifecycleStorage
import RumocaFMI3.Termination
import RumocaC.StorageRegion

/-! Public calls that a created instance accepts in every lifecycle segment
without selecting a solver step: Float64 accessors, empty accessors of the
other variable types and explicit termination. Each accepted request has one
deterministic returning behavior and an exact frame over the instance cells
(kind, mode, state and time), so every lifetime script composes it unchanged. -/
noncomputable section
namespace Rumoca.FMI3.InstanceQuery
open CMemory CCalls.Events

inductive Request where
  | access (buffers : Float64Buffers.Layout) (request : Float64Access.Request)
  | absent (ty : AbsentVariables.VariableType) (write : Bool) (references sizes values : Option Address)
  | terminate

/-- FMI 3.0.2 §§2.3.2-2.3.8 through the shared reference table: getters in
every mode, setters where the table permits them and termination from the
initialized simulation modes. -/
def Request.Allowed (request : Request) (kind : Kind) (mode : Mode) : Prop :=
  match request with
  | .access buffers request => request.Allowed kind mode ∧ request.Fits buffers
  | .absent _ write _ _ _ => Reference.Allowed (AbsentVariables.accessCommand write) kind mode
  | .terminate => Reference.Allowed .terminate kind mode

def Request.nextMode (request : Request) (mode : Mode) : Mode :=
  match request with
  | .terminate => .terminated
  | _ => mode

def Request.nextState (request : Request) (state : ModelExchange.State) : ModelExchange.State :=
  match request with
  | .access _ request => request.next state
  | _ => state

def Request.call (request : Request) (p : Address) : String × List Value :=
  match request with
  | .access buffers request => request.call p buffers
  | .absent ty write references sizes values =>
      ((AbsentVariables.signature ty write).name,
        AbsentVariables.arguments ty.hasSizes (some p) references sizes values 0 0)
  | .terminate => (Termination.signature.name, [.pointer (some p)])

/-- Typed host stores of reference/value arrays precede an accessor call. -/
def Request.hostRun (request : Request) (heap : Heap) : Option Heap :=
  match request with
  | .access buffers request => request.hostRun heap buffers
  | _ => some heap

def Request.after (model : Solve.FMI3Model source) (request : Request) (heap : Heap) (p : Address)
    (state : ModelExchange.State) (time : Binary64.Value) : Heap :=
  match request with
  | .access buffers request => request.after model heap p buffers state time
  | .absent _ _ _ _ _ => heap
  | .terminate => LifecycleBodies.writeMode heap p .terminated

def Request.readback (request : Request) (heap : Heap) : Nat → Option Value :=
  match request with
  | .access buffers request => request.readback heap buffers
  | _ => fun _ => none

/-- Selected values depend only on the Solve right-hand side. -/
def Request.expected (model : Solve.Model source) (request : Request)
    (state : ModelExchange.State) (time : Binary64.Value) : Nat → Option Value :=
  match request with
  | .access _ request => request.expected model.prepareFMI3 state time
  | _ => fun _ => none

/-- The caller-owned reference and value arrays of an accessor. -/
def Request.CallerRegion (request : Request) (q : Address) : Prop :=
  match request with
  | .access buffers _ => ¬ Float64Access.Outside buffers q
  | _ => False

/-- Original caller storage for the typed transfers. -/
def Request.Storage (request : Request) (heap : Heap) : Prop :=
  match request with
  | .access buffers _ => Float64Buffers.Stored heap buffers
  | _ => True

/-- Accessor arrays lie outside the instance record. -/
def Request.Separate (request : Request) (p : Address) : Prop :=
  match request with
  | .access buffers _ => buffers.Separate p
  | _ => True

structure QuietContract [CInterface] (model : Solve.FMI3Model source) (program : Program E) : Prop where
  get : ∀ heap, Float64Calls.QuietExecutionContract model program heap
  set : ∀ heap, Float64Set.QuietExecutionContract program heap
  absent : ∀ ty write, AbsentVariables.QuietContract ty write program
  terminate : Termination.QuietContract program

theorem Request.Storage.preserved {before later : Heap} (request : Request) (stored : request.Storage before)
    (storage : CStorage.PreservesOn request.CallerRegion before later) : request.Storage later := by
  cases request with
  | access buffers _ =>
    constructor
    · intro i hi
      obtain ⟨old, cell⟩ := stored.references i hi
      exact storage.cell (fun outside => outside.1 i hi rfl) cell
    · intro i hi
      obtain ⟨old, cell⟩ := stored.values i hi
      exact storage.cell (fun outside => outside.2 i hi rfl) cell
  | absent | terminate => trivial

theorem expected_solve (model : Solve.FMI3Model source) (request : Float64Access.Request)
    (state : ModelExchange.State) (time : Binary64.Value) :
    request.expected model state time = request.expected model.solve.prepareFMI3 state time := by
  cases request <;> rfl

theorem terminated_instance (stored : Float64Access.Instance heap p kind mode state time) :
    Float64Access.Instance (LifecycleBodies.writeMode heap p .terminated) p kind .terminated state time := by
  have field (name : String) (different : name ≠ "mode") :
      LifecycleBodies.writeMode heap p .terminated (p.member name) = heap (p.member name) :=
    LifecycleBodies.write_frame heap p _ .terminated (fun same => different ((Address.member_inj _ _ _).mp same))
  refine ⟨by simpa only [load, field "kind" (by decide)] using stored.kind, ?_, ?_,
    by simpa only [load, field "time" (by decide)] using stored.time⟩
  · simp [LifecycleBodies.writeMode, replace]
  · exact (LifecycleBodies.write_frame heap p _ .terminated (HistoryBodies.state_ne_field p "mode")).trans stored.state

/-- Every accepted request has exactly one behavior. Its post-state keeps
the instance cells except the selected state value and mode, writes only the
declared caller region and preserves storage types, read-only cells and leases. -/
theorem Request.step [CInterface] {program : Program E} (quiet : QuietContract model program)
    (request : Request) (stored : Float64Access.Instance heap p kind mode state time)
    (storage : request.Storage heap) (separate : request.Separate p) (allowed : request.Allowed kind mode) :
    let after := request.after model heap p state time
    ∃ ready, request.hostRun heap = some ready ∧
      (∀ behavior, (machine program).Behaves (.calling (request.call p).1 (request.call p).2 ready .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, after⟩) ∧
      Float64Access.Instance after p kind (request.nextMode mode) (request.nextState state) time ∧
      request.readback after = request.expected model.solve state time ∧
      CStorage.Preserves heap after ∧ CReadOnly.Preserves heap after ∧ CAtomicBoolean.Preserves heap after ∧
      (∀ q, q ≠ StateProofs.stateAddress p → q ≠ p.member "mode" → ¬ request.CallerRegion q → after q = heap q) := by
  cases request with
  | access buffers request =>
    obtain ⟨permitted, fits⟩ := allowed
    obtain ⟨host, called, instanceAfter, _, observes, preserved, readonly, frame⟩ :=
      Float64Access.step program quiet.get quiet.set request stored storage fits separate permitted
    refine ⟨_, host, called, instanceAfter,
      (Float64Access.Request.readback_correct observes).trans (expected_solve model request _ _), preserved, readonly,
      request.after_atomic model stored storage fits separate, ?_⟩
    intro q notState _ outside
    exact frame q notState (Classical.not_not.mp outside)
  | absent ty write references sizes values =>
    refine ⟨heap, rfl, quiet.absent ty write |>.empty heap p references sizes values kind mode
      stored.kind stored.mode_loaded allowed, ?_, rfl, .refl _, .refl _, .refl _, fun _ _ _ _ => rfl⟩
    simpa [Request.nextMode, Request.nextState] using stored
  | terminate =>
    obtain ⟨storage, readonly, atomic⟩ := LifecycleBodies.write_storage heap p _ .terminated stored.mode
    exact ⟨heap, rfl, quiet.terminate.successful heap p kind mode stored.kind stored.mode allowed,
      terminated_instance stored, rfl, storage, readonly, atomic,
      fun q _ notMode _ => LifecycleBodies.write_frame heap p q .terminated notMode⟩

end Rumoca.FMI3.InstanceQuery
end

noncomputable section
namespace Rumoca.FMI3.InstanceQuery
open CMemory

theorem Request.caller_block {request : Request} (separate : request.Separate p)
    (caller : request.CallerRegion q) : q.block ≠ p.block := by
  cases request with
  | access buffers _ =>
    intro same
    apply caller
    constructor
    · intro i _ equal
      subst equal
      exact separate.references same
    · intro i _ equal
      subst equal
      exact separate.values same
  | absent | terminate => exact caller.elim

theorem Request.Separate.rebase {request : Request} (separate : request.Separate p)
    (same : q.block = p.block) : request.Separate q := by
  cases request with
  | access buffers _ => exact ⟨same ▸ separate.references, same ▸ separate.values, separate.eachOther⟩
  | absent | terminate => trivial

theorem Request.not_record {request : Request} (separate : request.Separate p)
    (inside : p.InRecord q) : ¬ request.CallerRegion q :=
  fun caller => request.caller_block separate caller inside.1

/-- Co-Simulation Step and Terminated modes admit no start-value assignment,
so an accepted CS query retains the current sample. -/
theorem Request.cs_state {request : Request} (allowed : request.Allowed .cs mode)
    (simulating : mode = .step ∨ mode = .terminated) : request.nextState state = state := by
  cases request with
  | access buffers request =>
    cases request with
    | get => rfl
    | set values =>
      simp only [Request.nextState, Float64Access.Request.next]
      split
      · rename_i nonempty
        have setter := allowed.1
        simp only [Float64Access.Request.Allowed, Float64Access.Request.shape,
          if_neg (Nat.ne_of_gt nonempty)] at setter
        rcases simulating with rfl | rfl <;> simp [Reference.Allowed] at setter
      · rfl
  | absent | terminate => rfl

end Rumoca.FMI3.InstanceQuery
end
